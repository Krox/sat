module sat.sat;

private import core.bitop : popcnt;

private import std.stdio;
private import std.algorithm : move, min, max, sort, swap, canFind;
private import std.array : join;
private import std.conv : to;
private import std.algorithm : map;

private import jive.array;
private import jive.bitarray;
private import jive.lazyarray;
private import jive.queue;

private import math.statistics;
private import algo.graph;

public import sat.stats, sat.types, sat.clause, sat.solution;

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

	Solution solution; // (partial) solution, numbered with outer variable names

	// clauses
	bool contradiction; // empty clause
	Array!Lit units; // unit clauses
	Array!(Array!(Lit,uint)) bins; // binary clauses
	ClauseStorage clauses; // len >= 3 clauses

	this(int varCount = 0)
	{
		clauses = new ClauseStorage;
		solution = new Solution(varCount);
		varData.resize(varCount);
		bins.resize(varCount*2);
		for(int i = 0; i < varCount; ++i)
			varData[i].label = Lit(i, false);
	}

	int varCount() const @property
	{
		return cast(int)varData.length;
	}

	Lit addVar()
	{
		if(varCount != solution.varCount)
			throw new Exception("variable addition after renumbering not supported");
		Lit r = solution.addVar();
		varData.pushBack(VarData(0,false,r));
		bins.pushBack(Array!(Lit,uint).init);
		bins.pushBack(Array!(Lit,uint).init);
		return r;
	}

	size_t clauseCount() @property
	{
		size_t r = 0;
		if(contradiction)
			r += 1;
		foreach(ref c; clauses)
			r += 1;
		for(int i = 0; i < varCount*2; ++i)
			foreach(l; bins[Lit(i)])
				if(i >= l)
					++r;
		return r;
	}

	static struct ImplicationGraph
	{
		const Sat sat;

		int n() const @property
		{
			return 2 * sat.varCount;
		}

		static struct Range
		{
			const Sat sat;
			Lit l;

			int opApply(int delegate(int) dg) const
			{
				int r = 0;
				foreach(y; sat.bins[l.neg])
					if((r = dg(y.toInt)) != 0)
						break;
				return r;
			}
		}

		auto succ(int x) const
		{
			return Range(sat, Lit(x));
		}
	}

	auto implicationGraph() const
	{
		return ImplicationGraph(this);
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
	CRef addClauseRaw(const Lit[] c, bool irred)
	{
		// NOTE: do not sort the clause: c[0], c[1] might be there for a reason.

		// check it is well formed
		for(int i = 0; i < c.length; ++i)
		{
			assert(c[i].proper);
			for(int j = i+1; j < c.length; ++j)
				assert(c[i].var != c[j].var);
		}

		// special case for small stuff
		switch(c.length)
		{
			case 0: return addEmpty();
			case 1: return addClause(c[0]);
			case 2: return addClause(c[0], c[1]);
			default: break;
		}

		return clauses.addClause(c, irred);
	}

	/**
	 *  normalize a clause (duplicate lits, tautologies) and add it to the problem
	 *  returns index of new clause or CRef.undef for small implicit ones
	 */
	CRef addClause(const Lit[] c, bool irred)
 	{
		auto cl = Array!Lit(c[]);
		foreach(i, Lit l, ref bool rem; &cl.prune)
		{
			if(l == Lit.one)
				return CRef.undef;
			if(l == Lit.zero)
			{
				rem = true;
				continue;
			}

			for(size_t j = i+1; j < cl.length; ++j)
				if(l == cl[j])
				{
					rem = true;
					continue;
				}
				else if(l == cl[j].neg)
				{
					return CRef.undef;
				}
		}

		return addClauseRaw(cl[], irred);
 	}



	/** ditto */
	CRef addEmpty()
	{
		contradiction = true;
		return CRef.undef;
	}

	/** ditto */
	CRef addClause(Lit l)
	{
		if(l == Lit.one)
			return CRef.undef;
		if(l == Lit.zero)
			return addEmpty();

		assert(l.proper);
		units.pushBack(l);
		return CRef.undef;
	}

	/** ditto */
	CRef addClause(Lit a, Lit b)
	{
		if(a == Lit.one || b == Lit.one)
			return CRef.undef;
		if(a == Lit.zero)
			return addClause(b);
		if(b == Lit.zero)
			return addClause(a);

		assert(a.proper && b.proper);
		assert(a.var != b.var);
		bins[a].pushBack(b);
		bins[b].pushBack(a);
		return CRef.undef;
	}

	/** ditto */
	CRef addClause(Lit a, Lit b, Lit c, bool irred)
	{
		static Lit[3] cl;
		cl[0] = a;
		cl[1] = b;
		cl[2] = c;
		return addClause(cl[], irred);
	}

	/** add clauses encoding that k or more of the literals in c should be true */
	void addMinClause(const Lit[] c, int k, bool irred)
	{
		if(k <= 0)
			return;

		if(k == 1)
		{
			addClause(c, irred);
			return;
		}

		if(k == c.length)
		{
			foreach(x; c)
				addClause(x);
			return;
		}

		if(k > c.length)
		{
			addEmpty();
			return;
		}

		Array!Lit cl;
		assert(c.length <= 30);
		for(int sig = 0; sig < (1<<c.length); ++sig)
			if(popcnt(sig) == c.length-k+1)
			{
				cl.clear();
				for(int i = 0; i < c.length; ++i)
					if(sig & (1<<i))
						cl.pushBack(c[i]);
				addClause(cl[], irred);
			}
	}

	/** add clauses encoding that at most k of the literals in c should be true */
	void addMaxClause(const Lit[] c, int k, bool irred)
	{
		if(k >= c.length)
			return;

		if(k == 0)
		{
			foreach(x; c)
				addClause(x.neg);
			return;
		}

		if(k < 0)
		{
			addEmpty();
			return;
		}

		Array!Lit cl;
		assert(c.length <= 30);
		for(int sig = 0; sig < (1<<c.length); ++sig)
			if(popcnt(sig) == k+1)
			{
				cl.clear();
				for(int i = 0; i < c.length; ++i)
					if(sig & (1<<i))
						cl.pushBack(c[i].neg);
				addClause(cl[], irred);
			}
	}

	/** add clauses encoding that k of the literals in c should be true */
	void addCardClause(const Lit[] c, const int[] ks, bool irred)
	{
		auto cl = Array!Lit(c.length);
		for(int mask = 0; mask < (1<<c.length); ++mask)
			if(!canFind(ks, popcnt(mask)))
			{
				for(int i = 0; i < c.length; ++i)
					cl[i] = c[i]^((mask & (1<<i)) != 0);
				addClause(cl[], irred);
			}
	}

	void addXorClause(const Lit[] c, bool sign, bool irred)
	{
		auto cl = Array!Lit(c.length);
		for(int mask = 0; mask < (1<<c.length); ++mask)
			if((popcnt(mask)+sign)%2 != 0)
			{
				for(int i = 0; i < c.length; ++i)
					cl[i] = c[i]^((mask & (1<<i)) != 0);
				addClause(cl[], irred);
			}
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
			{
				addEmpty();
				rem = true;
			}
			else assert(x.proper);
		}

		// new bin content (may lead to units already in new name)
		auto newBins = Array!(Array!(Lit,uint))(newVarCount*2);
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
						addEmpty();
					else
					{
						assert(a.proper);
						units.pushBack(a);
					}
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
		}

		// new varData-array (this changes varCount, so do it last)
		auto newVarData = Array!VarData(newVarCount);
		for(int i = 0; i < varCount; ++i)
			if(!trans[i].fixed)
			{
				// already has a new name -> put equivalence in solution
				if(newVarData[trans[i].var].label != Lit.undef)
				{
					solution.setEquivalence(varData[i].label, newVarData[trans[i].var].label^trans[i].sign);
					continue;
				}

				newVarData[trans[i].var] = varData[i];
				if(trans[i].sign)
					newVarData[trans[i].var].flip;
			}
		varData = move(newVarData);
	}

	/** renumber accoring to currently known unary clauses */
	void renumber()
	{
		// contradiction -> remove all clauses
		if(contradiction)
		{
			foreach(ref l; bins[])
				l.resize(0);
			foreach(ref c; clauses)
				c.remove();
			units.resize(0);
			return;
		}

		if(units.empty)
			return;

		auto trans = Array!Lit(varCount, Lit.undef);

		foreach(x; units)
		{
			if(trans[x.var] == (Lit.one^x.sign))
				continue;
			else if(trans[x.var] == (Lit.zero^x.sign))
			{
				addEmpty();
				continue;
			}
			else
				assert(trans[x.var] == Lit.undef);

			trans[x.var] = Lit.one^x.sign;
			solution.setLiteral(toOuter(x));
		}

		int count = 0;
		for(int i = 0; i < varCount; ++i)
			if(trans[i] == Lit.undef)
				trans[i] = Lit(count++, false);

		renumber(trans[], count, false);
	}

	/** renumber for units and make all short clauses implicit */
	void cleanup()
	{
		swCleanup.start();
		scope(exit)
			swCleanup.stop();

		renumber();

		foreach(ref c; clauses)
			if(c.length < 3)
			{
				addClause(c[], c.irred);
				c.remove;
			}
	}

	/*
	 * remove some learnt clauses in order to not let it grow too much
	 * decisions are made on clause length. < 4 is always kept, >= 30 is always
	 * removes. Of those inbetween, the shortest n are kept.
	 */
	void clean(size_t n)
	{
		enum minLength = 4;
		enum maxLength = 30;

		Array!CRef[maxLength+1] list;
		foreach(i, ref c; clauses)
			if(!c.irred && c.length > minLength)
				if(c.length > maxLength)
					c.remove;
				else
					list[c.length].pushBack(i);

		for(int len = 0; len <= maxLength; ++len)
		{
			if(list[len].length > n)
			{
				foreach(i; list[len][n..$])
					clauses[i].remove;
				n = 0;
			}
			else
				n -= list[len].length;
		}
	}

	void print(File file)
	{
		file.writefln("p cnf %s %s", varCount, clauseCount);

		// empty clause
		if(contradiction)
			file.writefln("0");

		// unary clauses
		foreach(a; units)
			file.writefln("%s 0", a);

		// binary clauses
		for(int i = 0; i < varCount*2; ++i)
			foreach(l; bins[Lit(i)])
				if(i >= l)
					file.writefln("%s %s 0", Lit(i), l);

		// long clauses
		foreach(ref c; clauses)
			file.writefln("%s 0", c.toString);
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
		writefln("c ╔═══════════╤══════════╤══════════╤════════════════╤════════════════╗");
		writefln("c ║ conflicts │   vars   │  binary  │     long   len │   learnt   len ║");
		writefln("c ╟───────────┼──────────┼──────────┼────────────────┼────────────────╢");
	}

	void writeStatsLine()
	{
		auto histIrred = clauses.histogram(false);
		auto histLearnt = clauses.histogram(true);

		long nBin = 0;
		for(int i = 0; i < varCount; ++i)
		{
			nBin += bins[Lit(i,false)].length;
			nBin += bins[Lit(i,true)].length;
		}

		writefln("c ║ %#9s │ %#8s │ %#8s │ %#8s %#5.1f │ %#8s %#5.1f ║", nConflicts, varCount,
		         nBin, histIrred.count, histIrred.avg, histLearnt.count, histLearnt.avg);
	}

	void writeStatsFooter()
	{
		writefln("c ╚═══════════╧══════════╧══════════╧════════════════╧════════════════╝");
	}

	void writeComponentStats() const
	{
		int isolated = 0;
		Array!int s;

		auto comps = Components(implicationGraph);
		for(int i = 0; i < comps.nComps; ++i)
			if(comps.compSize[i] == 1)
				isolated++;
			else
				s.pushBack(comps.compSize[i]);

		sort!"a>b"(s[]);
		writef("c BIG components: ");
		foreach(x; s[])
			writef("%s ", x);
		writefln("(%s isolated points)", isolated);
	}
}
