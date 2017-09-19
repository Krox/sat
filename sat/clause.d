module sat.clause;

import core.stdc.string : memmove;
import std.algorithm : swap, map, sort;
import std.array : join;
import jive.array;

import sat.stats;
import sat.types;

struct Clause
{
	short length;
	ubyte flags;
	ubyte _reserved;

	enum FLAG_IRRED = 1;
	enum FLAG_MARKED = 2;
	enum FLAG_REMOVED = 4;

	bool irred() const @property { return (flags & FLAG_IRRED) != 0; }
	bool marked() const @property { return (flags & FLAG_MARKED) != 0; }
	bool removed() const @property { return (flags & FLAG_REMOVED) != 0; }
	void makeIrred() { flags |= FLAG_IRRED; }
	void makeRed() { flags &= ~FLAG_IRRED; }
	void mark() { flags |= FLAG_MARKED; }
	void unmark() { flags &= ~FLAG_MARKED; }
	void remove() { flags |= FLAG_REMOVED; }

	@disable this(this) {}

	private this(size_t len, bool irred)
	{
		assert(len <= short.max);
		this.length = cast(short)len;
		this.flags = irred;
	}

	inout(Lit)[] opSlice() inout
	{
		return (cast(inout(Lit)*)&this)[1..length+1];
	}

	ref inout(Lit) opIndex(size_t i) inout
	{
		return this[][i];
	}

	size_t opDollar() const
	{
		return length;
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
		return join(map!"a.toString"(this[]), " ");
	}

	bool opIn_r(Lit l) const
	{
		foreach(x; this[])
			if(l == x)
				return true;
		return false;
	}

	/** removes duplicate literals and marks tautology as removed */
	void normalize()
	{
		outer: for(int i = 0; i < length; ++i)
			for(int j = 0; j < i; ++j)
			{
				if(this[i] == this[j])
				{
					this[i] = this[$-1];
					length--;
					i--;
					continue outer;
				}
				else if(this[i] == this[j].neg)
				{
					this.remove();
					return;
				}
			}
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
		foreach(int k, Lit l; this[])
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
			this[pos] = this[$-1];
			--this.length;
		}
		else
			this[pos] = b;

		return !shorten;
	}

	/** remove a literal from a clause. Assumes/asserts that it was in */
	void removeLiteral(Lit a)
	{
		foreach(ref Lit l; this[])
			if(l == a)
			{
				l = this[$-1];
				--length;
				return;
			}
		assert(false);
	}
}

static assert(Clause.sizeof == Lit.sizeof);

struct CRef
{
	uint toInt = 0x3FFF_FFFF_U;

	enum CRef undef = CRef(0x3FFF_FFFF_U);
}

final class ClauseStorage
{
	private Array!Lit store;
	private Array!CRef clauses;

	this()
	{
		// TODO: non-initialized (and probably larger) reserve
		store.reserve(16*1024);
		clauses.reserve(1024);
	}

	this(ClauseStorage c)
	{
		store = c.store;
		clauses = c.clauses;
	}

	ref Clause opIndex(CRef r)
	{
		void* ptr = &store[r.toInt];
		return *cast(Clause*)ptr;
	}

	CRef addClause(const Lit[] lits, bool irred)
	{
		auto r = CRef(cast(int)store.length);
		auto header = Clause(lits.length, irred);
		store.pushBack(Lit(*cast(int*)&header));
		store.pushBack(lits);
		clauses.pushBack(r);
		return r;
	}

	CRef addClause(Lit a, Lit b, bool irred)
	{
		auto r = CRef(cast(int)store.length);
		auto header = Clause(2, irred);
		store.pushBack(Lit(*cast(int*)&header));
		store.pushBack(a);
		store.pushBack(b);
		clauses.pushBack(r);
		return r;
	}

	int opApply(int delegate(CRef, ref Clause) dg)
	{
		int r;
		foreach(i; clauses)
			if(!this[i].removed)
				if((r = dg(i, this[i])) != 0)
					return r;
		return 0;
	}

	int opApply(int delegate(ref Clause) dg)
	{
		int r;
		foreach(i; clauses)
			if(!this[i].removed)
				if((r = dg(this[i])) != 0)
					return r;
		return 0;
	}

	int opApplyReverse(int delegate(CRef, ref Clause) dg)
	{
		int r;
		foreach_reverse(i; clauses)
			if(!this[i].removed)
				if((r = dg(i, this[i])) != 0)
					return r;
		return 0;
	}

	int opApplyReverse(int delegate(ref Clause) dg)
	{
		int r;
		foreach_reverse(i; clauses)
			if(!this[i].removed)
				if((r = dg(this[i])) != 0)
					return r;
		return 0;
	}

	size_t memUsage() const @property
	{
		return store.memUsage + clauses.memUsage;
	}

	void compactify()
	{
		CRef j = CRef(0);
		foreach(ref i, ref bool rem; clauses.prune)
			if(this[i].removed)
				rem = true;
			else
			{
				memmove(&this[j], &this[i], uint.sizeof*(1+this[i].length));
				i = j;
				j.toInt += 1+this[i].length;
			}
		store.resize(j.toInt);
	}

	Histogram histogram(bool learnt)
	{
		Histogram h;
		foreach(ref c; this)
			if(c.irred != learnt)
				h.add(c.length);
		return h;
	}
}
