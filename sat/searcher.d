module sat.searcher;

/**
 * unit propagation, backtracking, conflict analysis, clause learning
 */

import std.stdio;
import std.datetime : Clock;
import std.algorithm : move, swap;

import jive.array;
import jive.lazyarray;
import jive.priorityqueue;

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
	}

	// NOTE: these are static just to save some allocation time
	static Array!VarData varData;
	static Array!(Array!CRef) watches; // watches into long clauses
	Array!Lit stack; // trail of set variables
	Array!int savePoint; // indices into stack
	static PriorityQueue!(int, ActivityComp, true) activityHeap; // variables by activity for branch decision

	static LazyBitArray seen; // temporary multi-purpose one bit pervariable. reset right before use

	Lit[] conflict; // conflict encountered, only valid after propagate(...) returned false
	private Lit[3] _conflict;

	ref lbool value(int i) const { return varData[i].value; }
	ref Reason reason(int i) const { return varData[i].reason; }
	ref int level(int i) const { return varData[i].level; }
	bool isSatisfied(Lit l) const { return varData[l.var].value == lbool(!l.sign); }
	int currLevel() const @property { return cast(int) savePoint.length; }

	this(Sat sat)
	{
		swSolverStartup.start();
		scope(exit)
			swSolverStartup.stop();

		this.sat = sat;
		assert(varCount > 0);

		watches.assign(2*varCount, Array!CRef.init);
		varData.assign(varCount, VarData.init);
		seen.resize(varCount);
		activityHeap.pred = ActivityComp(sat);
		activityHeap.clear();

		foreach(i, ref c; sat.clauses)
		{
			assert(c.length >= 3); // such should have been converted to implicit clauses
			watches[c[0]].pushBack(i);
			watches[c[1]].pushBack(i);
		}

		// NOTE: add units _after_ adding long clauses to get consistent watches
		foreach(l; sat.units)
		{
			if(isSatisfied(l))
				continue;
			if(isSatisfied(l.neg) || !propagate(l, Reason.undef))
			{
				sat.addEmpty();
				return;
			}
		}

		// add non-fixed variables to activity heap
		activityHeap.reserve(varCount);
		for(int i = 0; i < varCount; ++i)
			if(reason(i) == Reason.undef)
				activityHeap.push(i);
	}

	/**
	 * add a new clause to the solver and the underlying sat
	 *    - does not immediately propagate using the new clause
	 *    - returns reason appropriate for setting c[0] using the new clause
	 *    - sets watches on c[0] and c[1], so make sure that is okay
	 */
	Reason addClause(const Lit[] c)
	{
		CRef i = sat.addClause(c, false);

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
			if(lit.var !in activityHeap)
				activityHeap.push(lit.var);
		}
		savePoint.resize(l);
	}

	/* set a (previously unset) variable */
	private void set(Lit x, Reason r)
	{
		assert(value(x.var) == lbool.undef);
		value(x.var) = lbool(!x.sign);
		stack.pushBack(x);
		level(x.var) = currLevel;
		reason(x.var) = r;
		sat.varData[x.var].polarity = x.sign;
	}

	/** set a (previously unset) variable and propagate binaries. False on conflict. */
	private bool propagateBinary(Lit _x, Reason reason)
	{
		assert(value(_x.var) == lbool.undef);

		size_t pos = stack.length;

		set(_x, reason);

		while(pos != stack.length)
		{
			auto x = stack[pos++];

			// propagate binary clauses
			foreach(Lit y; sat.bins[x.neg])
			{
				// not set -> propagate
				if(value(y.var) == lbool.undef)
					set(y, Reason(x.neg));

				// set wrong -> conflict
				else if(isSatisfied(y.neg))
				{
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
			if(config.watchStats)
				watchHisto.add(watches[x.neg].length);
			outer: foreach(i, ref bool rem; &watches[x.neg].prune)
			{
				auto c = sat.clauses[i][];

				// move current variable to front position
				if(x.neg == c[1])
					swap(c[0], c[1]);
				assert(x.neg == c[0]);

				// other watch satisfied -> do nothing
				if(isSatisfied(c[1]))
					continue outer;

				foreach(ref y; c[2..$])
					if(!isSatisfied(y.neg)) // literal satisfied or undef -> move watch
					{
						swap(c[0], y);
						watches[c[0]].pushBack(i);
						rem = true;
						continue outer;
					}

				if(isSatisfied(c[1].neg)) // all literals false -> conflict
				{
					conflict = c;
					return false;
				}

				if(!propagateBinary(c[1], Reason(i))) // clause is unit -> propagate it
					return false;
			}
		}

		return true;
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
			if(lit.var in activityHeap)
				activityHeap.decrease(lit.var);

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

			if(--count == 0)
				break;

			switch(reason(stack[i].var).type)
			{
				case Reason.nil:
					break;

				case Reason.binary:
					visit(reason(stack[i].var).lit2);
					break;

				case Reason.clause:
					foreach(lit; sat.clauses[reason(stack[i].var).n])
						if(lit.var != stack[i].var)
							visit(lit);
					break;

				default:
					throw new Exception("invalid reason type in conflict analysis");
			}
		}

		buf[0] = stack[i].neg;

		// At this point the conflict clause consists of the asserting literal
		// in buf[0] (current level) and all seen[] literals in previous levels.
		// So we can use seen[] to strengthen the clause

		// strengthen the conflict clause using the reason clauses
		foreach(k, lit, ref bool rem; &buf.prune)
		{
			if(k == 0)
				continue;
			rem = isRedundant(lit);
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
		if(level(lit.var) == 0)
			return true;
		auto r = reason(lit.var);
		switch(r.type)
		{
			//case Reason.unary: assert(false); //return true;
			case Reason.binary: return seen[r.lit2.var];
			case Reason.clause:
				foreach(l; sat.clauses[r.n])
				if(!seen[l.var])
					return false;
			return true;
			case Reason.nil:
				return false;
			default: assert(false);
		}
	}

	/** most active undefined variable. -1 if everything is assigned */
	int mostActiveVariable()
	{
		while(!activityHeap.empty)
		{
			int v = activityHeap.pop;
			if(varData[v].value != lbool.undef)
				continue;

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
	bool run(int numConflicts)
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
				for(int v = 0; v < varCount; ++v)
					if(varData[v].value != lbool.undef) // non-decision variables (e.g. fixed/removed in sat) don't need to be set
						sat.addUnary(Lit(v, !cast(bool)varData[v].value));

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
				++nConflicts;
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
