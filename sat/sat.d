module sat.sat;

private import core.bitop : popcnt;

private import std.stdio;
private import std.algorithm : move, min, max, sort, swap;
private import std.array : join;
private import std.conv : to;
private import std.algorithm : map;

import jive.array;
import jive.bitarray;
import jive.lazyarray;
import jive.queue;

public import sat.stats, sat.types, sat.clause, sat.assignment;

/**
 *  - implicit unary and binary clauses
 *  - no occ-lists, watch-lists
 *  - no unit propagation !
 *  - variable meta-data (activity, polarity)
 */
final class Sat
{
	// activity / polarity is not actually used in this module,
	// but it needs to be persistent between solver restarts, so it is
	// stored here.
	static struct VarData
	{
		double activity = 0;
		bool polarity;
		Lit label = Lit.undef; // label for outside

		void flip()
		{
			polarity = !polarity;
			label = label.neg;
		}
	}
	Array!VarData varData;

	double activityInc = 1;

	Assignment assign;

	// clauses
	Array!Lit units; // unit clauses
	Array!(Array!Lit) bins; // binary clauses
	ClauseStorage clauses; // len >= 3 clauses

	this(int varCount)
	{
		clauses = new ClauseStorage;
		assign = new Assignment(varCount);
		varData.resize(varCount);
		bins.resize(varCount*2);
		for(int i = 0; i < varCount; ++i)
			varData[i].label = Lit(i, false);
	}

	int varCount() const @property
	{
		return cast(int)varData.length;
	}

	void bumpVariableActivity(int v)
	{
		varData[v].activity += activityInc;
	}

	void decayVariableActivity(double factor = 1.05)
	{
		activityInc *= factor;

		// scale everything down if neccessary
		if(activityInc > 1e100)
		{
			activityInc /= 1e100;
			for(int i = 0; i < varCount; ++i)
				varData[i].activity /= 1e100;
		}
	}

	Lit toOuter(Lit l) const
	{
		return varData[l.var].label^l.sign;
	}

	/**
	 *  add clause
	 *  assumes/asserts clause is syntactically well-formed (no duplicate variable)
	 *  returns index of new clause or CRef.undef for small implicit ones
	 */
	CRef addClause(const Lit[] c, bool irred)
	{
		if(c.length == 0)
			throw new Unsat;

		// NOTE: do not sort the clause: c[0], c[1] might be there for a reason.

		// check it is well formed
		for(int i = 0; i < c.length; ++i)
			for(int j = i+1; j < c.length; ++j)
				assert(c[i].var != c[j].var);

		// special case for small stuff
		switch(c.length)
		{
			case 0: throw new Unsat;
			case 1: return addUnary(c[0]);
			case 2: return addBinary(c[0], c[1]);
			default: break;
		}

		return clauses.addClause(c, irred);
	}

	/** ditto */
	CRef addUnary(Lit l)
	{
		units.pushBack(l);
		return CRef.undef;
	}

	/** ditto */
	CRef addBinary(Lit a, Lit b)
	{
		assert(a.var != b.var);
		bins[a].pushBack(b);
		bins[b].pushBack(a);
		return CRef.undef;
	}

	/** renumber according to trans, which should map old-var to new-lit */
	void renumber(const Lit[] trans, int newVarCount, bool hasDups)
	{
		// check input
		assert(trans.length == varCount);
		foreach(x; trans)
			assert(x.fixed || (x.proper && x.var < newVarCount));

		// renumber units
		foreach(ref x, ref bool rem; &units.prune)
		{
			x = trans[x.var]^x.sign;
			if(x == Lit.one)
				rem = true;
			else if(x == Lit.zero)
				throw new Unsat;
			else assert(x.proper);
		}

		// new bin content (may lead to units already in new name)
		auto newBins = Array!(Array!Lit)(newVarCount*2);
		foreach(i, ref list; bins)
		{
			Lit a = trans[Lit(cast(int)i).var]^Lit(cast(int)i).sign; // new name for Literal i

			if(a == Lit.one) // satisfied -> nothing to be done
				continue;

			// translate the list
			foreach(ref x, ref bool rem; &list.prune)
			{
				x = trans[x.var]^x.sign;
				if(x == Lit.one || x == a.neg) // (a or 1), (a or -a)
					rem = true;
				else if(x == Lit.zero || x == a) // (a or a), (a or 0)
				{
					if(a == Lit.zero)
						throw new Unsat;

					units.pushBack(a);
					rem = true;
				}
				else assert(x.proper);
			}

			if(a == Lit.zero)
				units.pushBack(list[]);
			else
			{
				assert(a.proper);
				newBins[a].pushBack(list[]);
			}
		}
		bins = move(newBins);

		// renumber long clauses
		outer: foreach(ref c; clauses)
		{
			for(int i = 0; i < c.length; ++i)
			{
				c[i] = trans[c[i].var]^c[i].sign;
				if(c[i] == Lit.one)
				{
					c.remove;
					continue outer;
				}
				if(c[i] == Lit.zero)
				{
					c[i] = c[$-1];
					c.length--;
					i--;
				}
			}

			if(hasDups)
			{
				c.normalize();
				if(c.removed)
					continue outer;
			}

			if(c.length <= 2)
			{
				addClause(c[], c.irred);
				c.remove;
			}
		}

		// new varData-array (this changes varCount, so do it last)
		auto newVarData = Array!VarData(newVarCount);
		for(int i = 0; i < varCount; ++i)
			if(!trans[i].fixed)
			{
				// already has a new name -> skip
				// (so that the new variable will have the label of the lowest
				//  old variable. Important to be consistent with the
				//  equivalences that twosat puts into the assignment)
				if(newVarData[trans[i].var].label != Lit.undef)
					continue;

				newVarData[trans[i].var] = varData[i];
				if(trans[i].sign)
					newVarData[trans[i].var].flip;
			}
		varData = move(newVarData);

	}

	void cleanup()
	{
		if(units.empty)
			return;

		swCleanup.start();
		scope(exit)
			swCleanup.stop();

		auto trans = Array!Lit(varCount, Lit.undef);

		foreach(x; units)
		{
			assign.setLiteral(toOuter(x)); // throws on contradicting units
			trans[x.var] = Lit.one^x.sign;
		}

		int count = 0;
		for(int i = 0; i < varCount; ++i)
			if(trans[i] == Lit.undef)
				trans[i] = Lit(count++, false);

		renumber(trans[], count, false);
	}

	void dump()
	{
		// unary clauses
		foreach(a; units)
			writefln("%s 0", a);

		// binary clauses
		for(int i = 0; i < varCount*2; ++i)
			foreach(l; bins[Lit(i)])
				if(i >= l)
					writefln("%s %s 0", Lit(i), l);

		// long clauses
		foreach(ref c; clauses)
			writefln("%s 0", c.toString);
	}

	bool checkSolution(ref const BitArray sol)
	{
		foreach(x; units)
			if(!sol[x])
				return false;

		for(int i = 0; i < varCount*2; ++i)
		{
			if(sol[Lit(i)])
				continue;
			foreach(x; bins[Lit(i)])
				if(!sol[x])
					return false;
		}

		outer: foreach(ref c; clauses)
		{
			foreach(x; c[])
				if(sol[x])
					continue outer;
			return false;
		}

		return true;
	}

	void writeStatsHeader()
	{
		writefln("c ╔═════════╤═══════════════════╤═══════════════╤═══════════════╗");
		writefln("c ║    vars │   binary  ternary │     long  len │   learnt  len ║");
		writefln("c ╟─────────┼───────────────────┼───────────────┼───────────────╢");
	}

	void writeStatsLine()
	{
		long nBin, nTer, nLong, nLearnt, nLitsLong, nLitsLearnt;

		for(int i = 0; i < varCount; ++i)
		{
			nBin += bins[Lit(i,false)].length;
			nBin += bins[Lit(i,true)].length;
		}
		nBin /= 2;

		foreach(ref c; clauses)
			if(c.length)
			{
				if(c.length == 3)
					++nTer;
				else if(c.irred)
				{
					nLitsLong += c.length;
					++nLong;
				}
				else
				{
					nLitsLearnt += c.length;
					++nLearnt;
				}
			}

		writefln("c ║ %#7s │ %#8s %#8s │ %#8s %#4.1f │ %#8s %#4.1f ║", varCount, nBin, nTer, nLong, cast(float)nLitsLong/nLong, nLearnt, cast(float)nLitsLearnt/nLearnt);
	}

	void writeStatsFooter()
	{
		writefln("c ╚═════════╧═══════════════════╧═══════════════╧═══════════════╝");
	}
}
