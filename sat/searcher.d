module sat.searcher;

/**
 * unit propagation, backtracking, conflict analysis, clause learning
 */

import std.stdio;
import std.datetime : Clock;
import std.algorithm : move, swap;

import jive.array;
import jive.bitarray;
import jive.priorityarray;

import sat.sat;

struct Reason
{
	enum
	{
		nil = 0x0000_0000_U,
		binary = 0x4000_0000_U,
		clause = 0x8000_0000_U,
	}

	enum dataMask = 0x3FFF_FFFF_U;
	enum typeMask = 0xC000_0000_U;

	uint data = nil;

	uint type() const nothrow @property @safe
	{
		return data & typeMask;
	}

	CRef n() const nothrow @property @safe
	{
		return CRef(data & dataMask);
	}

	Lit lit2() const nothrow @property @safe
	{
		return Lit(data & dataMask);
	}

	static enum Reason undef = Reason.init;

	this(Lit lit2)
	{
		assert((lit2.toInt & typeMask) == 0);
		this.data = lit2.toInt | binary;
	}

	this(CRef n)
	{
		assert((n.toInt & typeMask) == 0);
		this.data = n.toInt | clause;
	}
}

private struct ActivityComp
{
	Sat sat;

	this(Sat sat)
	{
		this.sat = sat;
	}

	bool opCall(int a, int b)
	{
		return sat.varData[a].activity > sat.varData[b].activity;
	}
}

/** NOTE: only one instance should exist at any time as global data is used to save allocation time */
final class Searcher
{
	Sat sat;
	int varCount() const @property { return sat.varCount; }

	static struct VarData
	{
		lbool value = lbool.undef;
		int level; // only valid for assigned variables
		Reason reason = Reason.undef; // ditto
		Lit dom = Lit.undef; // ditto
	}

	// NOTE: these are static just to save some allocation time
	static Array!VarData varData;
	static Array!(Array!CRef) watches; // watches into long clauses
	Array!Lit stack; // trail of set variables
	Array!int savePoint; // indices into stack
	static PriorityArray!(double, "a > b") activityArray; // variables by activity for branch decision

	static BitArray seen; // temporary multi-purpose, one bit per variable, reset right before use

	Lit[] conflict; // conflict encountered, only valid after propagate(...) returned false
	private Lit[3] _conflict;

	ref lbool value(int i) { return varData[i].value; }
	ref Reason reason(int i) { return varData[i].reason; }
	ref Lit dom(int i) { return varData[i].dom; }
	ref int level(int i) { return varData[i].level; }
	bool isSatisfied(Lit l) const { return varData[l.var].value == lbool(!l.sign); }
	int currLevel() const @property { return cast(int) savePoint.length; }

	this(Sat sat)
	{
		swSolverInit.start();
		scope(exit)
			swSolverInit.stop();

		this.sat = sat;
		assert(varCount > 0);

		watches.assign(2*varCount, Array!CRef.init);
		varData.assign(varCount, VarData.init);
		seen.resize(varCount);
		activityArray = PriorityArray!(double, "a > b")(varCount);

		foreach(i, ref c; sat.clauses)
		{
			assert(c.length >= 3); // such should have been converted to implicit clauses
			watches[c[0]].pushBack(i);
			watches[c[1]].pushBack(i);
		}

		// NOTE: add units _after_ adding long clauses to get consistent watches
		foreach(l; sat.units)
		{
			assert(l.proper);
			if(isSatisfied(l))
				continue;
			if(isSatisfied(l.neg) || !propagate(l, Reason.undef))
			{
				sat.addEmpty();
				return;
			}
		}

		// add non-fixed variables to activity heap
		for(int i = 0; i < varCount; ++i)
			if(value(i) == lbool.undef)
				activityArray[i] = sat.varData[i].activity;
			else
				activityArray[i] = -1;
	}

	/**
	 * add a new clause to the solver and the underlying sat
	 *    - does not immediately propagate using the new clause
	 *    - returns reason appropriate for setting c[0] using the new clause
	 *    - sets watches on c[0] and c[1], so make sure that is okay
	 */
	Reason addClause(const Lit[] c)
	{
		CRef i = sat.addClauseRaw(c, false);

		switch(c.length)
		{
			case 0:
				assert(false);

			case 1:
				return Reason.undef;

			case 2:
				return Reason(c[1]);

			default:
				watches[c[0]].pushBack(i);
				watches[c[1]].pushBack(i);
				return Reason(i);
		}
	}

	/** ditto */
	Reason addClause(Lit a, Lit b)
	{
		sat.addClause(a, b);
		return Reason(b);
	}

	void bumpLevel()
	{
		savePoint.pushBack(cast(int)stack.length);
	}

	/** unroll all assignments in levels > l, and set level to l */
	void unrollLevel(int l)
	{
		if(l == currLevel)
			return;
		assert(l < currLevel);
		while(stack.length > savePoint[l])
		{
			Lit lit = stack.popBack;
			value(lit.var) = lbool.undef;
			activityArray[lit.var] = sat.varData[lit.var].activity;
		}
		savePoint.resize(l);
	}

	/* set a (previously unset) variable */
	private void set(Lit x, Reason r, Lit d)
	{
		assert(value(x.var) == lbool.undef);
		value(x.var) = lbool(!x.sign);
		stack.pushBack(x);
		level(x.var) = currLevel;
		reason(x.var) = r;
		dom(x.var) = d;
		sat.varData[x.var].polarity = x.sign;
	}

	/** set a (previously unset) variable and propagate binaries. False on conflict. */
	private bool propagateBinary(Lit root, Reason reason)
	{
		size_t pos = stack.length;
		set(root, reason, root);

		while(pos != stack.length)
		{
			auto x = stack[pos++];

			// propagate binary clauses
			foreach(Lit y; sat.bins[x.neg])
			{
				// not set -> propagate
				if(value(y.var) == lbool.undef)
				{
					nBinProps++;
					set(y, Reason(x.neg), root);
				}

				// set wrong -> conflict
				else if(isSatisfied(y.neg))
				{
					nBinConfls++;
					_conflict[0] = x.neg;
					_conflict[1] = y;
					conflict = _conflict[0..2];
					return false;
				}
			}
		}

		return true;
	}

	/** set a (previously unset) variable and propagates everything. False on conflict. */
	private bool propagate(Lit _x, Reason reason)
	{
		assert(value(_x.var) == lbool.undef);

		size_t pos = stack.length;

		if(!propagateBinary(_x, reason))
			return false;

		while(pos != stack.length)
		{
			auto x = stack[pos++];

			// propagate long clauses
			watchHisto.add(watches[x.neg].length);
			outer: foreach(i, ref bool rem; watches[x.neg].prune)
			{
				auto c = sat.clauses[i][];

				// move current variable to position 1
				// (so that c[0] is the potentially propagated one)
				if(x.neg == c[0])
					swap(c[0], c[1]);
				assert(x.neg == c[1]);

				// other watch satisfied -> do nothing
				if(isSatisfied(c[0]))
					continue outer;

				foreach(ref y; c[2..$])
					if(!isSatisfied(y.neg)) // literal satisfied or undef -> move watch
					{
						swap(c[1], y);
						watches[c[1]].pushBack(i);
						rem = true;
						continue outer;
					}

				if(isSatisfied(c[0].neg)) // all literals false -> conflict
				{
					nLongConfls++;

					conflict = c;
					return false;
				}

				nLongProps++;
				auto reason = Reason(i);

				// try to replace long propagation by binary propagation
				if(config.hyperBinary)
				{
					auto dom = dominator(c[1..$]);
					if(dom != Lit.undef)
					{
						++nHyperBinary;
						reason = addClause(c[0], dom.neg);
					}
				}

				if(!propagateBinary(c[0], Reason(i))) // clause is unit -> propagate it
					return false;
			}
		}

		return true;
	}

	/** common dominator of assigned literals. Lit.undef if there is none */
	Lit dominator(Lit[] lits)
	{
		assert(lits.length >= 2); // pointless to do otherwise

		// check that a common dominator exists
		Lit d = Lit.undef;
		foreach(x; lits[])
			if(level(x.var) != 0)
			{
				if(d == Lit.undef)
					d = dom(x.var);
				else if(d != dom(x.var))
					return Lit.undef;
			}
		return d;
		/+ FIXME
		seen.reset();
		int count = 0;

		foreach(l; lits[])
		{
			if(level(l.var) == 0 || seen[l.var])
				continue;
			++count;
			seen[l.var] = true;
		}

		foreach_reverse(x; stack[])
		{
			if(!seen[x.var])
				continue;

			if(--count == 0)
			{
				assert(dom(x.var) == d);
				return x;
			}

			assert(reason(x.var).type == Reason.binary);
			auto y = reason(x.var).lit2;
			if(level(y.var) == 0 || seen[y.var])
				continue;

			++count;
			seen[y.var] = true;
		}
		assert(false);


		return dom(lits[0].var);
		+/
	}

	/**
	 * returns learnt clause as slice into a temporary buffer.
	 * clause[0] is the asserting literal.
	 * clause[1] has the highest level (if clause.length >= 2).
	 */
	Lit[] analyzeConflict()
	{
		assert(conflict !is null, "no conflict here to be analyzed");
		assert(currLevel > 0, "analyzing a conflict on level 0 does not make sense");

		seen.reset();
		static Array!Lit buf;
		buf.resize(1); // room for the asserting literal itself

		int count = 0;

		void visit(Lit lit)
		{
			if(seen[lit.var] || level(lit.var) == 0) // level 0 assignments are definite, so these variables can be skipped
				return;
			seen[lit.var] = true;

			sat.bumpVariableActivity(lit.var);
			if(activityArray[lit.var] != -1)
				activityArray[lit.var] = sat.varData[lit.var].activity;

			if(level(lit.var) < currLevel) // reason side
				buf.pushBack(lit);
			else // conflict side (includes the UIP itself)
				count++;
		}

		foreach(lit; conflict)
			visit(lit);

		int i = cast(int)stack.length;
		while(true)
		{
			--i;
			if(!seen[stack[i].var])
				continue;

			// only one variable on confict side left -> thats the UIP
			if(count-- == 1)
			{
				buf[0] = stack[i].neg;
				break;
			}

			// not the UIP -> do a resolution step
			switch(reason(stack[i].var).type)
			{
				case Reason.binary:
					visit(reason(stack[i].var).lit2);
					break;

				case Reason.clause:
					foreach(lit; sat.clauses[reason(stack[i].var).n])
						if(lit.var != stack[i].var)
							visit(lit);
					break;

				// NOTE: Reason.nil can only happen for the decision variable which will not be part of this analysis
				default:
					throw new Exception("invalid reason type in conflict analysis");
			}
		}

		// At this point the conflict clause consists of the asserting literal
		// in buf[0] (current level) and all seen[] literals in previous levels.
		// So we can use seen[] to strengthen the clause

		nLitsLearnt += buf.length;

		// strengthen the conflict clause using the reason clauses
		if(config.otf >= 1)
			foreach(k, lit, ref bool rem; buf.prune)
			{
				if(k == 0)
					continue;
				if(isRedundant(lit))
				{
					rem = true;
					nLitsOtfRemoved += 1;
				}
			}

		// move the highest level literal (excluding the asserting lit) to buf[1]
		if(buf.length > 1)
		{
			int m = 1;
			for(int k = 2; k < buf.length; ++k)
				if(level(buf[k].var) > level(buf[m].var))
					m = k;
			swap(buf[1], buf[m]);
		}

		conflict = null;
		sat.decayVariableActivity();
		return buf[];
	}

	// helper for OTF strengthening
	private bool isRedundant(Lit lit)
	{
		import std.stdio;

		assert(lit.proper);
		if(level(lit.var) == 0)
			return true;

		auto r = reason(lit.var);

		switch(r.type)
		{
			// descision variable -> cannot be removed
			case Reason.nil:
				return false;

			// otherwise, try to resolve it
			case Reason.binary:
				assert(r.lit2 != lit);
				return seen[r.lit2.var] || (config.otf >= 2 && isRedundant(r.lit2));
			case Reason.clause:
				foreach(l; sat.clauses[r.n])
					if(l != lit && !seen[l.var] && !(config.otf >= 2 && isRedundant(l)))
						return false;
				seen[lit.var] = true;
				return true;

			default: assert(false);
		}
	}

	/** most active undefined variable. -1 if everything is assigned */
	int mostActiveVariable()
	{
		while(activityArray.min != -1)
		{
			int v = cast(int)activityArray.minIndex;
			if(varData[v].value != lbool.undef)
			{
				activityArray[v] = -1;
				continue;
			}

			// check the heap (very expensive, debug only)
			//for(int i = 0; i < varCount; ++i)
			//	assert(assign[Lit(i,false)] || assign[Lit(i,true)] || activity[i] <= activity[v]);

			return v;
		}

		return -1;
	}

	/**
	 * Search for a solution using CDCL.
	 *    - returns true if solution or contradiction was found
	 *    - returns false if maximum number of conflicts was reached
	 */
	bool run(int numConflicts, ref Solution sol)
	{
		swSolver.start();
		scope(exit)
			swSolver.stop();

		if(sat.contradiction)
			return true;

		while(true)
		{
			// choose branching literal
			int branch = mostActiveVariable;

			// no branch -> we are done
			if(branch == -1)
			{
				sol = new Solution(sat.solution);

				for(int v = 0; v < varCount; ++v)
					if(varData[v].value != lbool.undef) // non-decision variables (e.g. fixed/removed in sat) don't need to be set
						sol.setLiteral(sat.toOuter(Lit(v, !cast(bool)varData[v].value)));
				sol.extend();
				unrollLevel(0);
				return true;
			}

			// propagate the decision
			bumpLevel();
			if(propagate(Lit(branch, sat.varData[branch].polarity), Reason.undef))
				continue;

			// analyze conflicts
			while(true)
			{
				if(currLevel == 0) // conflict on level 0 -> UNSAT
				{
					sat.addEmpty();
					return true;
				}

				auto conflictClause = analyzeConflict();
				auto reason = addClause(conflictClause[]);
				--numConflicts;
				++nLearnt;
				//writefln("conflict: %s", conflictClause[]);

				if(conflictClause.length == 1)
					unrollLevel(0);
				else
					unrollLevel(level(conflictClause[1].var));
				if(propagate(conflictClause[0], reason))
					break;
			}

			if(numConflicts <= 0)
			{
				unrollLevel(0);
				sat.units = stack;
				return false;
			}
		}

		assert(false);
	}
}
