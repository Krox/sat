module sat.sat;

private import core.bitop : popcnt;

private import std.stdio;
private import std.algorithm : move, min, max, sort, swap;
private import std.array : join;
private import std.conv : to;
private import std.algorithm : map;

import jive.array;
import jive.lazyarray;
import jive.queue;

public import sat.assignment;

struct Clause
{
	Array!Lit lits;
	alias lits this;
	ubyte flags;

	enum FLAG_IRRED = 1;
	enum FLAG_MARKED = 2;

	bool irred() const @property { return (flags & FLAG_IRRED) != 0; }
	bool marked() const @property { return (flags & FLAG_MARKED) != 0; }
	void makeIrred() { flags |= FLAG_IRRED; }
	void makeRed() { flags &= ~FLAG_IRRED; }
	void mark() { flags |= FLAG_MARKED; }
	void unmark() { flags &= ~FLAG_MARKED; }

	this(Array!Lit lits, bool irred)
	{
		this.lits = move(lits);
		this.flags = irred;
	}

	uint signs() const @property
	{
		assert(length <= 32);
		uint r = 0;
		foreach(i, l; this)
			if(l.sign)
				r |= 1U << i;
		return r;
	}

	string toString() const @property
	{
		return join(map!"a.toString"(lits[]), " ");
	}

	/**
	 * replace literal a by b in this clause (both a and b have to b proper literals)
	 *   - assumes/asserts that a is contained and b.neg is not contained
	 *   - returns false if b was already in (so it shrinked)
	 *   - returns true otherwise
	 */
	bool replaceLiteral(Lit a, Lit b)
	{
		assert(a.var != b.var);
		assert(b.proper);
		assert(length);

		int pos = -1;
		bool shorten = false;
		foreach(int k, Lit l; lits[])
		{
			if(l == a)
				pos = k;
			if(l == b)
				shorten = true;

			assert(l != b.neg);
		}

		assert(pos != -1);

		if(shorten) // b was already in -> clause becomes shorter
		{
			swap(lits[pos], lits.back);
			lits.popBack;
		}
		else
			lits[pos] = b;

		return !shorten;
	}
}

final class Sat
{
	Assignment assign;
	int varCount() const @property { return cast(int)renum.length; }

	Array!Clause clauses;		// length=0 means clause was removed
	private Array!(Array!int) occList;	// can contain clauses from which the literal was removed (or the clause itself can be removed). Also duplicates are possible.
	Array!int occCountIrred;
	Array!int occCountRed;

	private Array!(Array!Lit) binaryClauses;	// binary clauses. NOTE: can sometimes be asymmetric
	Array!bool binaryDirty;		// indicates that a binary-list may contain removed/fixed variables
	Array!bool binaryNew;	// indicates that there are new binary clauses, on which tarjan has not run yet
	bool binaryAnyNew = false;

	static struct Propagation { Lit a; Lit b; } // replace literal a with b (a is proper, b can be proper or Lit.one)
	Queue!Propagation prop;		// propagation queue

	bool varRemoved = false;	// indicates whether a variable/clause was removed since the last run of cleanup()
	bool clauseRemoved = false;

	Array!int renum; // inner -> outer

	Array!double activity;
	double activityInc = 1;

	Array!bool polarity;

	/** NOTE: clauseCount is only an estimate */
	this(int varCount, int clauseCount = 0)
	{
		renum.resize(varCount);
		for(int i = 0; i < varCount; ++i)
			renum[i] = i;

		clauses.reserve(clauseCount);
		assign = new Assignment(varCount);
		rebuildOccLists();
		binaryClauses.resize(varCount*2);
		binaryDirty.resize(varCount*2);
		binaryNew.resize(varCount*2);
		activity.resize(varCount, 0);
		polarity.resize(varCount, false);
	}

	int[] occs(Lit lit)
	{
		if(occCount(lit) != occList[lit].length) // the list is dirty, clean it up before returning it
		{
			sort(occList[lit][]);
			int last = -1;
			foreach(int k, ref bool rem; &occList[lit].prune)
			{
				rem = !clauses[k].lits.containsValue(lit) || (k == last);
				last = k;
			}
		}

		assert(occCount(lit) == occList[lit].length, "corrupt occCount. lit = "~to!string(lit));
		return occList[lit][];
	}

	/** same as occs(lit).length, but faster */
	size_t occCount(Lit lit) const
	{
		return occCountIrred[lit] + occCountRed[lit];
	}

	void rebuildOccLists()
	{
		occList.resize(varCount*2);
		foreach(ref list; occList)
			list.resize(0);
		occCountIrred.resize(varCount*2);
		occCountRed.resize(varCount*2);
		occCountIrred[] = 0;
		occCountRed[] = 0;

		foreach(int i, ref c; clauses)
			foreach(l; c)
			{
				occList[l].pushBack(i);
				if(c.irred)
					occCountIrred[l]++;
				else
					occCountRed[l]++;
			}
	}

	/** put a clause into the appropriate occ lists */
	void attachClause(int i)
	{
		assert(clauses[i].length, "tried to attach a removed clause");

		bool irred = clauses[i].irred;
		foreach(x; clauses[i][])
		{
			occList[x].pushBack(i);
			if(irred)
				occCountIrred[x]++;
			else
				occCountRed[x]++;
		}
	}

	/** (lazily) remove a clause from its occ lists */
	void detachClause(int i)
	{
		bool irred = clauses[i].irred;
		foreach(l; clauses[i][])
			if(irred)
				occCountIrred[l]--;
			else
				occCountRed[l]--;
	}

	ref Array!Lit bins(Lit lit)
	{
		// clean up if neccessary
		if(binaryDirty[lit])
		{
			sort(binaryClauses[lit][]);
			Lit last = Lit.undef;
			foreach(x, ref bool rem; &binaryClauses[lit].prune)
			{
				rem = binaryClauses[x].empty || x == last;
				last = x;
			}
			binaryDirty[lit] = false;
		}

		return binaryClauses[lit];
	}

	Lit toOuter(Lit l)
	{
		return Lit(renum[l.var], l.sign);
	}

	/** need to call rebuildOccLists() after renumber() */
	void renumber()
	{
		auto trans = Array!int(varCount, -1); // old -> new
		int count = 0;
		for(int i = 0; i < varCount; ++i)
			if(assign[Lit(renum[i], false)] == Lit.undef)
				trans[i] = count++;

		assert(prop.empty);
		for(int i = 0; i < varCount*2; ++i)
			foreach(ref l; bins(Lit(i))) // NOTE: bins(..) makes sure all lazy-removed is gone
				l = Lit(trans[l.var], l.sign);
		foreach(ref c; clauses)
			foreach(ref l; c)
				l = Lit(trans[l.var], l.sign);

		foreach(i, ref list, ref bool rem; &binaryClauses.prune)
			if(trans[Lit(cast(int)i).var] == -1)
				rem = true;

		foreach(i, x, ref bool rem; &renum.prune)
			if(trans[i] == -1)
				rem = true;

		foreach(i, x, ref bool rem; &activity.prune)
			if(trans[i] == -1)
				rem = true;

		foreach(i, x, ref bool rem; &polarity.prune)
			if(trans[i] == -1)
				rem = true;
	}

	void bumpVariableActivity(int v)
	{
		activity[v] += activityInc;
	}

	void decayVariableActivity()
	{
		activityInc *= 1.05;
		if(activityInc > 1e100)
		{
			activityInc /= 1e100;
			activity[][] /= 1e100;
		}
	}

	/** renumber variables and make new occ-lists */
	void cleanup()
	{
		if(propagate())
			writefln("c WARNING: not fully propagated before cleanup"); // no problem, just a question of style

		if(clauseRemoved)
			foreach(ref c, ref bool rem; &clauses.prune)
				if(c.length == 0)
					rem = true;

		if(varRemoved)
			renumber();

		if(clauseRemoved || varRemoved)
			rebuildOccLists();

		clauseRemoved = false;
		varRemoved = false;
	}

	/** replace a by b */
	void setEquivalence(Lit a, Lit b)
	{
		assert(a.proper && b.proper);
		assign.setEquivalence(toOuter(a), toOuter(b));
		prop.push(Propagation(a, b));
	}

	/** returns number of vars propagated */
	uint propagate()
	{
		uint count = 0;

		while(!prop.empty)
		{
			++count;
			auto p = prop.pop();

			assert(renum[p.a.var] != -1 && assign[toOuter(p.a)] != Lit.undef, "tried to propagate a variable that is already fixed/eliminated");

			if(p.b == Lit.one) // fix literal p.a
			{
				foreach(lit; bins(p.a.neg))
					addUnary(lit);

				foreach(k; occs(p.a))
					removeClause(k);
				foreach(k; occs(p.a.neg))
					removeLiteral(k, p.a.neg);
			}
			else // replace literal p.a with p.b
			{
				assert(p.b.proper);

				foreach(lit; bins(p.a))
					addBinary(p.b, lit);
				foreach(lit; bins(p.a.neg))
					addBinary(p.b.neg, lit);

				foreach(i; occs(p.a))
					replaceLiteral(i, p.a, p.b);
				foreach(i; occs(p.a.neg))
					replaceLiteral(i, p.a.neg, p.b.neg);
			}

			assert(occs(p.a).length == 0);
			assert(occs(p.a.neg).length == 0);

			foreach(lit; bins(p.a))
				binaryDirty[lit] = true;
			foreach(lit; bins(p.a.neg))
				binaryDirty[lit] = true;

			binaryClauses[p.a].resize(0);
			binaryClauses[p.a.neg].resize(0);
			binaryDirty[p.a] = false;
			binaryDirty[p.a.neg] = false;

			renum[p.a.var] = -1;
		}

		if(count)
			varRemoved = true;

		return count;
	}

	/** remove literal a from clause i */
	void removeLiteral(int i, Lit a)
	{
		if(!clauses[i].removeValue(a))
			assert(false, "literal to be deleted was not found");

		if(clauses[i].irred)
			occCountIrred[a]--;
		else
			occCountRed[a]--;

		if(clauses[i].length == 2)
		{
			addBinary(clauses[i][0], clauses[i][1]);
			removeClause(i);
		}
		else assert(clauses[i].length > 2);
	}

	/** replace a by b in clause i (both a and b have to b proper literals) */
	void replaceLiteral(int i, Lit a, Lit b)
	{
		if(clauses[i].containsValue(b.neg))
			return removeClause(i);

		if(clauses[i].irred)
			occCountIrred[a]--;
		else
			occCountRed[a]--;

		if(clauses[i].replaceLiteral(a,b))
		{
			occList[b].pushBack(i);
			if(clauses[i].irred)
				occCountIrred[b]++;
			else
				occCountRed[b]++;
		}
		else
		{
			if(clauses[i].length == 2)
			{
				addBinary(clauses[i][0], clauses[i][1]);
				removeClause(i);
			}
		}
	}

	/** add a unary clause, i.e. fix a literal */
	void addUnary(Lit l)
	{
		if(!assign.setLiteral(toOuter(l)))
			return;
		prop.push(Propagation(l, Lit.one));
	}

	/** add a binary clause */
	void addBinary(Lit a, Lit b)
	{
		if(a == b)
			return addUnary(a);
		else if(a == b.neg)
			return;

		binaryClauses[a].pushBack(b);
		binaryClauses[b].pushBack(a);
		binaryNew[a] = true;
		binaryNew[b] = true;
		binaryAnyNew = true;
	}

	/** add a ternary clause */
	void addTernary(Lit a, Lit b, Lit c)
	{
		Lit[3] cl;
		cl[0] = a;
		cl[1] = b;
		cl[2] = c;
		addClause(cl[], true);
	}

	/**
	 *  add clause of arbitrary length
	 *  returns index of new clause
	 *  returns -1 on tautologies and small implicitly stored clauses
	 */
	int addClause(const Lit[] c, bool irred)
	{
		if(c.length == 0)
			throw new Unsat;

		// NOTE: do not sort the clause: c[0], c[1] might be there for a reason.

		// check for tautology
		for(int i = 0; i < c.length; ++i)
			for(int j = i+1; j < c.length; ++j)
			{
				assert(c[i] != c[j]);
				if(c[i] == c[j].neg)
					return -1;
			}

		if(c.length == 1)
		{
			addUnary(c[0]);
			return -1;
		}

		if(c.length == 2)
		{
			addBinary(c[0], c[1]);
			return -1;
		}

		clauses.pushBack(Clause(Array!Lit(c), irred));
		attachClause(cast(int)clauses.length-1);
		return cast(int)clauses.length-1;
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
				addUnary(x);
			return;
		}

		if(k > c.length)
			throw new Unsat;

		Array!Lit cl;
		assert(c.length <= 30);
		for(int sig = 0; sig < (1<<c.length); ++sig)
			if(popcnt(sig) == c.length-k+1)
			{
				assert(cl.empty);
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
				addUnary(x.neg);
			return;
		}

		if(k < 0)
			throw new Unsat;

		Array!Lit cl;
		assert(c.length <= 30);
		for(int sig = 0; sig < (1<<c.length); ++sig)
			if(popcnt(sig) == k+1)
			{
				assert(cl.empty);
				for(int i = 0; i < c.length; ++i)
					if(sig & (1<<i))
						cl.pushBack(c[i].neg);
				addClause(cl[], irred);
			}
	}

	/** remove clause i */
	void removeClause(int i)
	{
		assert(clauses[i].length);
		clauseRemoved = true;
		detachClause(i);
		clauses[i].resize(0);
	}

	/** mark clause i as irreducible */
	void makeClauseIrred(int i)
	{
		if(clauses[i].irred)
			return;
		clauses[i].makeIrred();
		foreach(l; clauses[i])
		{
			occCountRed[l]--;
			occCountIrred[l]++;
		}
	}

	/** find clause or any subclause. -1 if not found. signs is relative to signs of c */
	// TODO: enable it to find binary clauses
	int findClause(const ref Clause c, uint signs = 0)
	{
		assert(prop.empty);
		static LazyArray!ubyte buf;
		assert(c.length <= 32);

		buf.resize(clauses.length);
		buf.reset();

		foreach(i, l; c)
			foreach(j; occs(l^((signs&(1<<i))!=0)))
				if(clauses[j].length <= c.length)
					if(++buf[j] == clauses[j].length)
						return j;
		return -1;
	}

	/** check consitency of occ-lists. for debugging */
	void check()
	{
		assert(prop.empty);

		size_t count = 0;
		for(int i = 0; i < varCount*2; ++i)
		{
			foreach(k; occs(Lit(i)))
				assert(clauses[k].lits.containsValue(Lit(i)));

			count += occs(Lit(i)).length;
		}

		foreach(ref c; clauses)
			count -= c.length;

		assert(count == 0);
		writefln("c check okay");
	}

	void dump()
	{
		for(int i = 0; i < varCount*2; ++i)
			foreach(l; bins(Lit(i)))
				if(i >= l)
					writefln("%s %s 0", Lit(i), l);
		foreach(ref c; clauses)
			if(c.length)
				writefln("%s 0", c);
	}

	void writeStatsHeader()
	{
		writefln("╔═════════╤═══════════════════╤═══════════════╤═══════════════╗");
		writefln("║    vars │   binary  ternary │     long  len │   learnt  len ║");
		writefln("╟─────────┼───────────────────┼───────────────┼───────────────╢");
	}

	void writeStatsLine()
	{
		long nBin, nTer, nLong, nLearnt, nLitsLong, nLitsLearnt;

		for(int i = 0; i < varCount; ++i)
		{
			nBin += bins(Lit(i,false)).length;
			nBin += bins(Lit(i,true)).length;
		}
		nBin /= 2;

		for(int i = 0; i < clauses.length; ++i)
			if(clauses[i].length)
			{
				if(clauses[i].length == 3)
					++nTer;
				else if(clauses[i].irred)
				{
					nLitsLong += clauses[i].length;
					++nLong;
				}
				else
				{
					nLitsLearnt += clauses[i].length;
					++nLearnt;
				}
			}

		writefln("║ %#7s │ %#8s %#8s │ %#8s %#4.1f │ %#8s %#4.1f ║", varCount, nBin, nTer, nLong, cast(float)nLitsLong/nLong, nLearnt, cast(float)nLitsLearnt/nLearnt);
	}

	void writeStatsFooter()
	{
		writefln("╚═════════╧═══════════════════╧═══════════════╧═══════════════╝");
	}
}
