module sat;

import std.stdio;
import std.conv;
import jive.array;
import jive.flatset;
private import std.algorithm : move, min, max;
import solver, clause;
import std.parallelism;

class Sat
{
	const string name;
	Array!(FlatSet!int) clauses;	// length=0 means clause was removed
	Array!(Array!int) occs;	// can contain removed clauses
	Array!bool assign;
	int varCount;

	void writeAssignment()
	{
		writef("v");
		for(int i = 0; i < varCount; ++i)
			if(assign[2*i])
				writef(" %s", i+1);
			else
				writef(" -%s", i+1);
		writefln(" 0");
	}

	void setVariable(int x)
	{
		if(assign[x^1])
			throw new Unsat;
		if(assign[x])
			return;
		assign[x] = true;

		auto occsPos = move(occs[x]);
		auto occsNeg = move(occs[x^1]);

		foreach(i; occsPos)
			removeClause(i);

		foreach(i; occsNeg)
		{
			clauses[i].remove(x^1);
			if(clauses[i].length == 1)
				setVariable(clauses[i][0]);
		}
	}

	/** returns false if the clause is trivial, satisfied or unit */
	bool normalizeClause(ref FlatSet!int c)
	{
		foreach(x, ref bool rem; &c.prune)
		{
			if(assign[x])
				return false;
			if(assign[x^1])
				rem = true;
		}

		if(c.length == 0)
			throw new Unsat;

		if(c.length == 1)
		{
			setVariable(c[0]);
			return false;
		}

		for(size_t i = 1; i < c.length; ++i)
			if(c[i] == (c[i-1]^1))
				return false;

		return true;
	}

	void addClause(FlatSet!int c)
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
		assign.resize(2*varCount);
		occs.resize(2*varCount);

		Array!int c;

		for(int i = 0; i < clauseCount; ++i)
		{
			while(true)
			{
				int x;
				if(f.readf(" %s", &x) != 1)
					throw new Exception("read error");
				if(x==0) break;
				assert(-varCount<=x && x <= varCount);
				x = x>0 ? 2*x-2 : -2*x-1;
				c.pushBack(x);
			}

			addClause(FlatSet!int(c[]));
			c.resize(0);
		}
	}

	void dump()
	{
		foreach(ref c; clauses)
		{
			foreach(x; c)
				writef("%s ", x&1?-((x>>1)+1):((x>>1)+1));
			writefln("0");
		}
	}

	void solve()
	{
		auto renum = new int[2*varCount];
		renum[] = -1;
		int j = 0;
		for(int x = 0; x < 2*varCount; x+=2)
			if(!assign[x] && !assign[x^1])
			{
				renum[x] = j;
				renum[x^1] = j^1;
				j += 2;
			}

		if(j == 0)
		{
			writefln("c all variables set in preprocessing");
			return;
		}

		auto db = new ClauseDB(j/2);
		foreach(ci, ref c; clauses)
			if(c.length)
		{
			int buf[500];
			foreach(size_t i, x; c)
				buf[i] = renum[x];
			db.addClause(buf[0..c.length]);
		}

		auto sol = (new Solver(db)).solve();
		if(sol is null)
			throw new Unsat;

		for(int x = 0; x < 2*varCount; x+=2)
		if(renum[x] != -1)
		{
			assign[x] = sol[renum[x]];
			assign[x^1] = sol[renum[x]^1];
		}
	}

	static void solve(string filename)
	{
		auto sat = new Sat(filename);
		try
		{
			sat.readFile();
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
