module sat.sat;

import jive.array;
import jive.lazyarray;
import jive.queue;
import jive.flatset;
private import std.stdio;
private import std.math : abs;
private import std.algorithm : move, min, max;
private import std.bitmanip : bitfields;
private import std.array : join;
private import std.conv : to;
private import std.range : map;
import sat.clause, sat.solver;

struct Lit
{
	uint toInt;
	alias toInt this;
	static assert(Lit.sizeof == uint.sizeof);
	// NOTE: don't use std.bitmanip:bitfields. The asserts it contains are more annoying than helpful

	this(uint v, bool s)
	{
		toInt = (v<<1) | s;
	}

	private this(uint i)
	{
		toInt = i;
	}

	uint var() const @property
	{
		return toInt >> 1;
	}

	void var(uint v) @property
	{
		toInt = (toInt & 1) | (v << 1);
	}

	bool sign() const @property
	{
		return toInt & 1;
	}

	void sign(bool s) @property
	{
		toInt = (toInt & ~1) | s;
	}

	Lit neg() const @property
	{
		return Lit(toInt ^ 1);
	}

	int toDimacs() const @property
	{
		if(sign)
			return -(var+1);
		else
			return var+1;
	}

	string toString() const @property
	{
		switch(this.toInt)
		{
			case nil: return "nil";
			case one: return "true";
			case zero: return "false";
			default: return to!string(toDimacs);
		}
	}

	static Lit fromDimacs(int x)
	{
		Lit l;
		l.sign = x<0;
		l.var = abs(x)-1;
		return l;
	}

	static enum Lit nil = Lit(-1);
	static enum Lit one = Lit(-2, false);
	static enum Lit zero = Lit(-2, true);
	static assert(one.fixed);
	static assert(zero.fixed);

	bool fixed() const @property
	{
		return (toInt&~1) == -4;
	}

	bool proper() const @property
	{
		return (toInt & (1U<<31)) == 0;
	}
}

struct Clause
{
	FlatSet!Lit lits;
	alias lits this;

	this(Array!Lit lits)
	{
		this.lits = FlatSet!Lit(move(lits));
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
	Array!Clause clauses;	// length=0 means clause was removed
	Array!(Array!int) occs;	// can contain removed clauses
	Array!Lit var;			// nil if undef, fixed if fixed, actual literal if equivalence
	Queue!uint prop;		// propagation queue
	int varCount;

	/** NOTE: clauseCount is only an estimate */
	this(int varCount, int clauseCount = 0)
	{
		this.varCount = varCount;
		var.resize(varCount, Lit.nil);
		occs.resize(2*varCount);
		clauses.reserve(clauseCount);
	}

	Lit rootLiteral(Lit l)
	{
		while(l.proper && var[l.var] != Lit.nil)
			if(l.sign)
				l = var[l.var].neg;
			else
				l = var[l.var];
		return l;
	}

	bool isSatisfied(const Lit[] c)
	{
		foreach(l; c)
			if(rootLiteral(l) == Lit.one)
				return true;
		return false;
	}

	void writeAssignment()
	{
		writef("v");
		for(uint v = 0; v < varCount; ++v)
		{
			Lit l = rootLiteral(Lit(v,false));
			assert(l.fixed, "tried to output incomplete assignment");
			writef(" %s", Lit(v, l.sign).toDimacs);
		}
		writefln(" 0");
	}

	void setLiteral(Lit l)
	{
		l = rootLiteral(l);

		if(l == Lit.one)
			return;

		if(l == Lit.zero)
			throw new Unsat;

		assert(var[l.var] == Lit.nil);
		if(!l.sign)
			var[l.var] = Lit.one;
		else
			var[l.var] = Lit.zero;
		prop.push(l.var);
	}

	void setEquivalence(Lit a, Lit b)
	{
		a = rootLiteral(a);
		b = rootLiteral(b);

		// if both are the same variable or both are fixed, there is nothing to do
		if(a.var == b.var)
			if(a.sign == b.sign)
				return;
			else
				throw new Unsat;

		// if one is fixed, just set the other one
		if(a.fixed)
			return setLiteral(Lit(b.var, b.sign^a.sign));
		if(b.fixed)
			return setLiteral(Lit(a.var, a.sign^b.sign));

		// otherwise, we have an actual equivalence
		assert(var[a.var] == Lit.nil);
		assert(var[b.var] == Lit.nil);
		var[b.var] = Lit(a.var, a.sign^b.sign);
		prop.push(b.var);
	}

	/** returns number of vars propagated */
	uint propagate()
	{
		uint count = 0;
		while(!prop.empty)
		{
			++count;
			Lit a = Lit(prop.pop(), false);
			Lit b = rootLiteral(a);
			assert(a.var != b.var);

			//writefln("c propagating %s -> %s", a, b);

			foreach(i; move(occs[a]))
				replaceOcc(i, a, b);
			foreach(i; move(occs[a.neg]))
				replaceOcc(i, a.neg, b.neg);
		}

		return count;
	}

	void replaceOcc(int i, Lit a, Lit b)
	{
		assert(a.proper);
		assert(b != Lit.nil);

		if(clauses[i].length == 0)
			return;

		assert(a in clauses[i].lits);

		if(b == Lit.one)
			return removeClause(i);

		if(!clauses[i].remove(a))
			assert(false, "corrupt occ-list");

		if(b != Lit.zero)
			if(clauses[i].add(b))
				occs[b].pushBack(i);

		if(clauses[i].length == 1)
			setLiteral(clauses[i][0]);

		if(clauses[i].tautological)
			removeClause(i);
	}

	void addClause(Array!Lit c)
	{
		foreach(ref l, ref bool rem; &c.prune)
		{
			l = rootLiteral(l);
			if(l == Lit.one)
				return;
			else if(l == Lit.zero)
				rem = true;
			else
				assert(l.proper);
		}

		if(c.length == 0)
			throw new Unsat;

		auto d = Clause(move(c));

		if(d.length == 1)
		{
			setLiteral(d[0]);
			return;
		}

		if(d.tautological)
			return;

		foreach(x; d)
			occs[x].pushBack(cast(int)clauses.length);
		clauses.pushBack(move(d));
	}

	void removeClause(int i)
	{
		auto c = move(clauses[i]);	// this sets clauses[i].length = 0, i.e. marks it as removed
	}

	/** find clause or any subclause. -1 if not found. signs is relative to signs of c */
	int findClause(const ref Clause c, uint signs = 0)
	{
		static LazyArray!ubyte buf;
		assert(c.length <= 256);

		buf.resize(clauses.length);
		buf.reset();

		foreach(i, l; c)
			foreach(j; occs[Lit(l.var, l.sign != ((signs&(1<<i))!=0))])
				if(0 < clauses[j].length && clauses[j].length <= c.length)
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

	void solve()
	{
		auto renum = new int[varCount];
		renum[] = -1;
		int j = 0;
		for(int v = 0; v < varCount; ++v)
			if(var[v] == Lit.nil)
				renum[v] = j++;

		if(j == 0)
		{
			writefln("c all variables set in preprocessing");
			return;
		}

		auto db = new ClauseDB(j);
		foreach(ci, ref c; clauses)
			if(c.length)
		{
			Lit buf[256];
			foreach(size_t i, x; c)
			{
				assert(renum[x.var] != -1, "problem still contains removed variable: "~x.toString);
				buf[i] = Lit(renum[x.var], x.sign);
			}
			db.addClause(buf[0..c.length]);
		}

		auto sol = (new Solver(db)).solve();
		if(sol is null)
			throw new Unsat;

		for(int v = 0; v < varCount; ++v)
		if(renum[v] != -1)
		{
			assert(var[v] == Lit.nil);
			if(sol[Lit(renum[v], false)])
				var[v] = Lit.one;
			else if(sol[Lit(renum[v], true)])
				var[v] = Lit.zero;
			else assert(false);
		}
	}
}

class Unsat : Exception
{
	this()
	{
		super("answer is unsat");
	}
}
