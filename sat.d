module sat;

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
import clause, solver;

struct Lit
{
	union
	{
		uint toInt;
		mixin(bitfields!(
			bool, "sign", 1,
			uint, "var", 31
			));
	}

	alias toInt this;

	this(uint var, bool sign)
	{
		this.var = var;
		this.sign = sign;
	}

	int toDimacs() const @property
	{
		if(sign)
			return -(var+1);
		else
			return var+1;
	}

	static Lit fromDimacs(int x)
	{
		Lit l;
		l.sign = x<0;
		l.var = abs(x)-1;
		return l;
	}

	Lit neg() const @property
	{
		return Lit(var, !sign);
	}
}

struct Clause
{
	FlatSet!Lit lits;
	alias lits this;

	this(Lit[] lits)
	{
		this.lits = lits;
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
		return join(map!"to!string(a.toDimacs)"(lits[]), " ");
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
	Array!VarState var;
	Queue!uint prop;	// propagation queue
	int varCount;

	enum : uint
	{
		undef = 0,
		set,
		eq,
	}

	struct VarState
	{
		mixin(bitfields!(
			uint, "state", 2,
			bool, "sign", 1,
			uint, "eq", 29
			));
	}

	/** NOTE: clauseCount is only an estimate */
	this(int varCount, int clauseCount = 0)
	{
		this.varCount = varCount;
		var.resize(varCount);
		occs.resize(2*varCount);
		clauses.reserve(clauseCount);
	}

	Lit rootLiteral(Lit l)
	{
		while(var[l.var].state == eq)
		{
			l.sign = l.sign ^ var[l.var].sign;
			l.var = var[l.var].eq;
		}
		return l;
	}

	bool isSatisfied(Lit l)
	{
		l = rootLiteral(l);
		return var[l.var].state == set && (var[l.var].sign == l.sign);
	}

	bool isSatisfied(const ref Clause c)
	{
		foreach(l; c)
			if(isSatisfied(l))
				return true;
		return false;
	}

	bool isSatisfied(const ref Array!Clause cs)
	{
		foreach(ref c; cs)
			if(!isSatisfied(c))
				return false;
		return true;
	}

	void writeAssignment()
	{
		writef("v");
		for(uint v = 0; v < varCount; ++v)
		{
			Lit l =  rootLiteral(Lit(v,false));
			assert(var[l.var].state == set, "tried to output incomplete assignment");
			writef(" %s", Lit(v, var[l.var].sign ^ l.sign).toDimacs);
		}
		writefln(" 0");
	}

	void setLiteral(Lit l)
	{
		l = rootLiteral(l);

		if(var[l.var].state == set)
		{
			if(var[l.var].sign == l.sign)
				return;
			else
				throw new Unsat;
		}

		assert(var[l.var].state == undef);
		var[l.var].state = set;
		var[l.var].sign = l.sign;
		prop.push(l.var);
	}

	void setEquivalence(Lit a, Lit b)
	{
		a = rootLiteral(a);
		b = rootLiteral(b);
		bool sign = a.sign^b.sign;
		uint v = a.var, w = b.var;

		if(v == w)
			if(sign)
				throw new Unsat;
			else
				return;

		if(var[v].state == set)
			return setLiteral(Lit(w, var[v].sign^sign));
		if(var[w].state == set)
			return setLiteral(Lit(v, var[w].sign^sign));

		assert(var[v].state == undef);
		assert(var[w].state == undef);
		var[w].state = eq;
		var[w].eq = v;
		var[w].sign = sign;
		prop.push(w);
	}

	/** returns number of vars propagated */
	uint propagate()
	{
		uint count = 0;
		while(!prop.empty)
		{
			++count;
			uint v = prop.pop();

			if(var[v].state == set)
			{
				bool s = var[v].sign;
				auto occsPos = move(occs[Lit(v,s)]);
				auto occsNeg = move(occs[Lit(v,!s)]);

				foreach(i; occsPos)
					removeClause(i);

				foreach(i; occsNeg)
					if(clauses[i].length)
					{
						if(!clauses[i].remove(Lit(v,!s)))
							assert(false, "corrupt occ-list found while propagating");

						if(clauses[i].length == 1)
							setLiteral(clauses[i][0]);
					}
			}
			else if(var[v].state == eq)
			{
				Lit a = Lit(v,false);
				Lit b = rootLiteral(a);
				assert(a != b);

				foreach(i; move(occs[a]))
					replaceOcc(i, a, b);
				foreach(i; move(occs[a.neg]))
					replaceOcc(i, a.neg, b.neg);
			}
			else assert(false);
		}

		return count;
	}

	void addClause(Clause c)
	{
		foreach(l, ref bool rem; &c.prune)
			if(var[l.var].state == set)
				if(var[l.var].sign == l.sign)
					return;
				else
					rem = true;
			else assert(var[l.var].state == undef);

		if(c.length == 0)
			throw new Unsat;

		if(c.length == 1)
		{
			setLiteral(c[0]);
			return;
		}

		if(c.tautological)
			return;

		foreach(x; c)
			occs[x].pushBack(cast(int)clauses.length);
		clauses.pushBack(move(c));
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


	void replaceOcc(int i, Lit a, Lit b)
	{
		if(clauses[i].remove(a) && clauses[i].add(b))
			occs[b].pushBack(i);
		if(clauses[i].length == 1)
			setLiteral(clauses[i][0]);
		if(clauses[i].tautological)
			clauses[i].resize(0);
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
			if(var[v].state == undef)
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
			int buf[500];
			foreach(size_t i, x; c)
			{
				assert(renum[x.var] != -1, "problem still contains removed variables");
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
			assert(var[v].state == undef);
			var[v].state = set;
			if(sol[Lit(renum[v], false)])
				var[v].sign = false;
			else if(sol[Lit(renum[v], true)])
				var[v].sign = true;
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
