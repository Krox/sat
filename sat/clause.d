module sat.clause;

import std.algorithm : join, swap, map, sort;
import jive.array;
import sat.assignment : Lit;

struct Clause
{
	short length;
	ubyte flags;
	ubyte _reserved;

	enum FLAG_IRRED = 1;
	enum FLAG_MARKED = 2;

	bool irred() const @property { return (flags & FLAG_IRRED) != 0; }
	bool marked() const @property { return (flags & FLAG_MARKED) != 0; }
	void makeIrred() { flags |= FLAG_IRRED; }
	void makeRed() { flags &= ~FLAG_IRRED; }
	void mark() { flags |= FLAG_MARKED; }
	void unmark() { flags &= ~FLAG_MARKED; }

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
	int v = -1;

	int opCast(T)()
		if(is(T == int))
	{
		return v;
	}

	bool proper() const @property
	{
		return v >= 0;
	}

	enum CRef undef = CRef(-1);
	enum CRef taut = CRef(-2);	// tautological clause
	enum CRef implicit = CRef(-3); // implicit clause (i.e. binary/ternary which is stored directly inside watchlists or so)
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

	ref Clause opIndex(CRef r)
	{
		void* ptr = &store[cast(int)r];
		return *cast(Clause*)ptr;
	}

	CRef add(const Lit[] lits, bool irred)
	{
		auto r = CRef(cast(int)store.length);
		auto header = Clause(lits.length, irred);
		store.pushBack(Lit(*cast(int*)&header));
		store.pushBack(lits);
		clauses.pushBack(r);
		return r;
	}

	int opApply(int delegate(CRef, ref Clause) dg)
	{
		int r;
		foreach(i; clauses)
			if(this[i].length)
				if((r = dg(i, this[i])) != 0)
					return r;
		return 0;
	}

	int opApply(int delegate(ref Clause) dg)
	{
		int r;
		foreach(i; clauses)
			if(this[i].length)
				if((r = dg(this[i])) != 0)
					return r;
		return 0;
	}
}
