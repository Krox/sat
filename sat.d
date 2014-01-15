module sat;

import std.stdio;
import std.conv;
import jive.array;
import jive.queue;
import jive.flatset;
private import std.math : abs;
private import std.algorithm : move, min, max;
private import std.bitmanip : bitfields;
import solver, clause;
import std.parallelism;

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


class Sat
{
	alias FlatSet!Lit Clause;
	const string name;
	Array!Clause clauses;	// length=0 means clause was removed
	Array!(Array!int) occs;	// can contain removed clauses
	Array!VarState var;
	Queue!uint prop;	// propagation queue
	int varCount;

	enum : uint
	{
		undef = 0,
		set,
	}

	struct VarState
	{
		mixin(bitfields!(
			uint, "state", 2,
			bool, "sign", 1,
			uint, "eq", 29
			));
	}

	void writeAssignment()
	{
		writef("v");
		for(uint v = 0; v < varCount; ++v)
		{
			assert(var[v].state == set);
			writef(" %s", Lit(v, var[v].sign).toDimacs);
		}
		writefln(" 0");
	}

	void setLiteral(Lit l)
	{
		if(var[l.var].state == set)
		{
			if(var[l.var].sign == l.sign)
				return;
			else
				throw new Unsat;
		}

		var[l.var].state = set;
		var[l.var].sign = l.sign;
		prop.push(l.var);
	}

	void propagate()
	{
		while(!prop.empty)
		{
			uint v = prop.pop();
			assert(var[v].state == set);
			bool s = var[v].sign;

			auto occsPos = move(occs[Lit(v,s)]);
			auto occsNeg = move(occs[Lit(v,!s)]);

			foreach(i; occsPos)
				removeClause(i);

			foreach(i; occsNeg)
			{
				clauses[i].remove(Lit(v,!s));
				if(clauses[i].length == 1)
					setLiteral(clauses[i][0]);
			}
		}
	}

	/** returns false if the clause is trivial, satisfied or unit */
	bool normalizeClause(ref Clause c)
	{
		foreach(l, ref bool rem; &c.prune)
			if(var[l.var].state == set)
				if(var[l.var].sign == l.sign)
					return false;
				else
					rem = true;

		if(c.length == 0)
			throw new Unsat;

		if(c.length == 1)
		{
			setLiteral(c[0]);
			return false;
		}

		for(size_t i = 1; i < c.length; ++i)
			if(c[i] == c[i-1].neg)
				return false;

		return true;
	}

	void addClause(Clause c)
	{
		if(!normalizeClause(c))
			return;
		foreach(x; c)
			occs[x].pushBack(cast(int)clauses.length);
		clauses.pushBack(move(c));
	}

	void removeClause(int i)
	{
		auto c = move(clauses[i]);	// this sets clauses[i].length = 0, i.e. marks it as removed
	}

	private this(string filename)
	{
		name = filename;
	}

	void readFile()
	{
		auto f = File(name, "r");
		int clauseCount;

		loop: while(true)
		{
			string foo;
			if(f.readf("%s ", &foo) != 1)
				throw new Exception("file read error");

			switch(foo)
			{
				case "c":
					f.readln();
					break;

				case "p":
					if(f.readf(" cnf %s %s\n", &varCount, &clauseCount) != 2)
						throw new Exception("file read error");
					break loop;

				default: throw new Exception("unexpected line in file starting with \""~foo~"\"");
			}
		}

		writefln("c reading file %s: v=%s c=%s", name[max(0,cast(int)$-50)..$], varCount, clauseCount);

		clauses.reserve(clauseCount);
		var.resize(varCount);
		occs.resize(2*varCount);

		Array!Lit c;

		for(int i = 0; i < clauseCount; ++i)
		{
			while(true)
			{
				int x;
				if(f.readf(" %s", &x) != 1)
					throw new Exception("read error");
				if(x==0) break;
				assert(-varCount<=x && x <= varCount);
				c.pushBack(Lit.fromDimacs(x));
			}

			addClause(Clause(c[]));
			c.resize(0);
		}
	}

	void dump()
	{
		foreach(ref c; clauses)
		{
			foreach(x; c)
				writef("%s ", x.toDimacs);
			writefln("0");
		}
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
				buf[i] = Lit(renum[x.var], x.sign);
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

	static void solve(string filename)
	{
		auto sat = new Sat(filename);
		try
		{
			sat.readFile();
			sat.propagate();
			sat.solve();
			writefln("s SATISFIABLE");
			sat.writeAssignment();
		}
		catch(Unsat e)
		{
			writefln("s UNSATISFIABLE");
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
