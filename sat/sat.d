module sat.sat;

import jive.array;
import jive.lazyarray;
import jive.queue;
import jive.flatset;
private import std.stdio;
private import std.algorithm : move, min, max;
private import std.array : join;
private import std.conv : to;
private import std.range : map;

public import sat.assignment;

struct Clause
{
	FlatSet!Lit lits;
	alias lits this;
	bool irred;

	this(Array!Lit lits, bool irred)
	{
		this.lits = FlatSet!Lit(move(lits));
		this.irred = irred;
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

	bool tautological() const @property
	{
		for(size_t i = 1; i < length; ++i)
			if(this[i].var == this[i-1].var)
				return true;
		return false;
	}
}

final class Sat
{
	Assignment assign;
	int varCount() const @property { return assign.varCountInner; }

	Array!Clause clauses;		// length=0 means clause was removed
	Array!(Array!int) occList;	// can contain clauses, from which the literal was removed (or the clause itself can be removed)
	Array!int occCountIrred;	// number of removed elements in occList
	Array!int occCountRed;		// number of removed elements in occList

	static struct Propagation { int v; Lit lit; } // replace variable v by lit (which might be Lit.zero/one)
	Queue!Propagation prop;		// propagation queue

	bool varRemoved = false;	// indicates whether a variable/clause was removed since the last run of cleanup()
	bool clauseRemoved = false;

	/** NOTE: clauseCount is only an estimate */
	this(int varCount, int clauseCount = 0)
	{
		clauses.reserve(clauseCount);
		assign = new Assignment(varCount);
		rebuildOccLists();
	}

	int[] occs(Lit lit)
	{
		if(occCount(lit) != occList[lit].length) // the list is dirty, clean it up before returning it
			foreach(int k, ref bool rem; &occList[lit].prune)
				rem = (lit !in clauses[k].lits);

		assert(occCount(lit) == occList[lit].length, "corrupt occCount");
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

	/** need to call rebuildOccLists() after renumber() */
	void renumber()
	{
		foreach(ref c; clauses)
			foreach(ref l; c)
				l = assign.toOuter(l);

		assign.renumber();

		foreach(ref c; clauses)
			foreach(ref l; c)
				l = assign.toInner(l);
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

	void setLiteral(Lit l)
	{
		if(!assign.setLiteralInner(l))
			return;
		prop.push(Propagation(l.var, Lit.one^l.sign));
	}

	/** replace a by b */
	void setEquivalence(Lit a, Lit b)
	{
		assert(a.proper && b.proper);
		assign.setEquivalenceInner(a, b);
		prop.push(Propagation(a.var, b^a.sign));
	}

	/** returns number of vars propagated */
	uint propagate()
	{
		uint count = 0;

		while(!prop.empty)
		{
			++count;
			auto p = prop.pop();
			auto a = Lit(p.v, false);
			auto b = p.lit;

			foreach(i; occs(a))
				replaceOcc(i, a, b);
			foreach(i; occs(a.neg))
				replaceOcc(i, a.neg, b.neg);

			occList[a].resize(0);
			occList[a.neg].resize(0);
			assert(occCountRed[a] == 0 && occCountIrred[a] == 0 && occCountRed[a.neg] == 0 && occCountIrred[a.neg] == 0);
		}

		if(count)
			varRemoved = true;

		return count;
	}

	/**
	 * replace a by b in clause i
	 *    - a has to be a proper literal
	 *    - b can be Lit.zero/Lit.one (effectively removes the literal/clause)
	 */
	void replaceOcc(int i, Lit a, Lit b)
	{
		assert(a.proper);
		assert(b.proper || b.fixed);
		assert(a in clauses[i].lits);

		if(b == Lit.one)
		{
			removeClause(i);
			return;
		}

		if(clauses[i].irred)
			occCountIrred[a]--;
		else
			occCountRed[a]--;

		if(!clauses[i].remove(a))
			assert(false, "corrupt occ-list");

		if(b != Lit.zero)
			if(clauses[i].add(b))
			{
				occList[b].pushBack(i);
				if(clauses[i].irred)
					occCountIrred[b]++;
				else
					occCountRed[b]++;
			}

		if(clauses[i].length == 1)
			setLiteral(clauses[i][0]);

		if(clauses[i].tautological)
			removeClause(i);
	}

	void addClause(Array!Lit c, bool irred)
	{
		foreach(ref l, ref bool rem; &c.prune)
		{
			if(l == Lit.one)
				return;
			else if(l == Lit.zero)
				rem = true;
			else
				assert(l.proper);
		}

		if(c.length == 0)
			throw new Unsat;

		auto d = Clause(move(c), irred);

		if(d.length == 1)
		{
			setLiteral(d[0]);
			return;
		}

		if(d.tautological)
			return;

		foreach(x; d)
		{
			occList[x].pushBack(cast(int)clauses.length);
			if(irred)
				occCountIrred[x]++;
			else
				occCountRed[x]++;
		}
		clauses.pushBack(move(d));
	}

	Clause removeClause(int i)
	{
		assert(clauses[i].length != 0);
		foreach(l; clauses[i])
			if(clauses[i].irred)
				occCountIrred[l]--;
			else
				occCountRed[l]--;
		clauseRemoved = true;
		return move(clauses[i]);
	}

	void makeClauseIrred(int i)
	{
		if(clauses[i].irred)
			return;
		clauses[i].irred = true;
		foreach(l; clauses[i])
		{
			occCountRed[l]--;
			occCountIrred[l]++;
		}
	}

	/** find clause or any subclause. -1 if not found. signs is relative to signs of c */
	int findClause(const ref Clause c, uint signs = 0)
	{
		static LazyArray!ubyte buf;
		assert(c.length <= 256);

		buf.resize(clauses.length);
		buf.reset();

		foreach(i, l; c)
			foreach(j; occs(Lit(l.var, l.sign != ((signs&(1<<i))!=0))))
				if(clauses[j].length <= c.length)
					if(++buf[j] == clauses[j].length)
						return j;
		return -1;
	}

	void dump()
	{
		foreach(ref c; clauses)
			if(c.length)
				writefln("%s 0", c);
	}
}

class Timeout : Exception
{
	this()
	{
		super("solver timed out");
	}
}
