module sat;

import std.stdio;
import std.conv;
import jive.array;
private import std.algorithm : move, min, max;
import solver, clause;
import std.parallelism;

class Sat
{
	const string name;
	Array!(Array!int) clauses;	// length=0 means clause was removed
	Array!bool assign;
	bool dirty;		// true if there is an assignment that is not fully propagated yet
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
		dirty = true;
		assign[x] = true;
	}

	/** returns false if the clause is trivial, satisfied or unit */
	bool normalizeClause(ref Array!int c)
	{
		foreach(x, ref bool rem; &c.prune)
		{
			if(assign[x])
				return false;
			if(assign[x^1])
				rem = true;
		}

		c.makeSet();

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

	void addClause(Array!int c)
	{
		if(normalizeClause(c))
			clauses.pushBack(move(c));
	}

	this(string filename)
	{
		//writefln("loading %s", filename);
		name = filename;
		auto f = File(filename, "r");
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

		clauses.reserve(clauseCount);
		assign.resize(2*varCount);

		for(int i = 0; i < clauseCount; ++i)
		{
			Array!int c;

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

			addClause(move(c));
		}
	}

	/** remove tautological clauses and do unit propagation */
	void cleanup()
	{
		if(!dirty)
			return;
		dirty = false;

		foreach(ref c; clauses)
			if(c.length)
				if(!normalizeClause(c))
					c.resize(0);

		cleanup();
	}

	// set pure literals
	void pureLiteral()
	{
		Array!(Array!int) occs;
		occs.resize(2*varCount);

		start:
		foreach(int i, ref c; clauses)
			foreach(x; c)
				occs[x].pushBack(i);

		bool change = false;

		for(int x = 0; x < varCount*2; x += 2)
			if(!assign[x] && !assign[x^1])
			{
				if(occs[x].empty)
				{
					change = true;
					assign[x^1] = true;
					foreach(i; occs[x^1])
						clauses[i].resize(0);
				}
				else if(occs[x^1].empty)
				{
					change = true;
					assign[x] = true;
					foreach(i; occs[x])
						clauses[i].resize(0);
				}
			}

		if(change)	// if done something, prune clauses and redo
		{
			foreach(ref c, ref bool rem; &clauses.prune)
				rem = c.empty;
			for(int x = 0; x < varCount*2; ++x)
				occs[x].resize(0);
			goto start;
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
		writefln("c solving %s: v=%s c=%s", name[max(0,cast(int)$-50)..$], varCount, clauses.length);

		cleanup();	// actually not worth it on my testcases, but not by much, so I keep it

		//pureLiteral();	// not worth it either, but more seriously

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
		if(sol !is null)
		{
			for(int x = 0; x < 2*varCount; x+=2)
			if(renum[x] != -1)
			{
				assign[x] = sol[renum[x]];
				assign[x^1] = sol[renum[x]^1];
			}

			writefln("s SATISFIABLE");
			writeAssignment();
		}
		else
			writefln("s UNSATISFIABLE");
	}
}

class Unsat : Exception
{
	this()
	{
		super("answer is unsat");
	}
}
