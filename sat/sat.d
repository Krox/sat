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

public import sat.assignment;
public import sat.clause;

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
		Lit label; // label for outside

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

		// check its is well formed
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

		return clauses.add(c, irred);
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
	void renumber(const Lit[] trans, int newVarCount)
	{
		// new varData-array
		auto newVarData = Array!VarData(newVarCount);
		for(int i = 0; i < varCount; ++i)
			if(!trans[i].fixed)
			{
				newVarData[trans[i].var] = varData[i];
				if(trans[i].sign)
					newVarData[trans[i].var].flip;
			}

		// new bin content
		foreach(i, ref list; bins)
			foreach(ref x, ref bool rem; &list.prune)
			{
				x = trans[x.var]^x.sign;
				if(x == Lit.one)
					rem = true;
				if(x == Lit.zero)
				{
					units.pushBack(Lit(cast(int)i));
					rem = true;
				}
			}

		// new bin-arrays
		auto newBins = Array!(Array!Lit)(newVarCount*2);
		for(int i = 0; i < varCount; ++i)
		{
			if(trans[i].fixed)
				units.pushBack(bins[Lit(i, trans[i].sign).neg][]);
			else
			{
				if(newBins[trans[i]^false].empty)
					newBins[trans[i]^false] = move(bins[Lit(i,false)]);
				else
					newBins[trans[i]^false].pushBack(bins[Lit(i,false)][]);

				if(newBins[trans[i]^true].empty)
					newBins[trans[i]^true] = move(bins[Lit(i,true)]);
				else
					newBins[trans[i]^true].pushBack(bins[Lit(i,true)][]);
			}
		}
		bins = move(newBins);

		// renumber units (after binary in order to renumber freshly propagated units)
		foreach(ref x, ref bool rem; &units.prune)
		{
			x = trans[x.var]^x.sign;
			if(x == Lit.one)
				rem = true;
			if(x == Lit.zero)
				throw new Unsat;
		}

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

			if(c.length <= 2)
			{
				addClause(c[], c.irred);
				c.remove;
			}
		}

		varData = move(newVarData); // this changes varCount, so do it last
	}

	void cleanup()
	{
		if(units.empty)
			return;

		auto trans = Array!Lit(varCount, Lit.undef);
		foreach(x; units)
		{
			assign.setLiteral(varData[x.var].label^x.sign); // throws on contradicting units
			trans[x.var] = Lit.one^x.sign;
		}

		int count = 0;
		for(int i = 0; i < varCount; ++i)
			if(trans[i] == Lit.undef)
				trans[i] = Lit(count++, false);

		renumber(trans[], count);
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
