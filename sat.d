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
	Array!(Array!int) clauses;
	Array!(Array!int) clausesOriginal;	// unaltered clauses for final check
	Array!bool assign;
	int varCount;

	void test()
	{
		for(int x = 0; x < 2*varCount; x+=2)
		{
			if(!assign[x] && !assign[x^1])
				throw new Exception("incomplete assignment on variable "~to!string(x));

			if(assign[x] && assign[x^1])
				throw new Exception("invalid assignment");
		}

		outer: foreach(ref c; clausesOriginal)
		{
			foreach(x; c)
				if(assign[x])
					continue outer;

			throw new Exception("final check failed");
		}

		writefln("final check ok");
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

			clauses.pushBack(move(c));
		}

		clausesOriginal = clauses;
	}

	// remove duplicates and tautological clauses and do unit propagation
	void cleanup()
	{
		foreach(ref c, ref bool remClause; &clauses.prune)
		{
			c.makeSet();

			for(size_t i = 1; i < c.length; ++i)
				if(c[i] == (c[i-1]^1))
				{
					remClause = true;
					break;
				}
		}

		while(true)
		{
			bool change = false;

			outer: foreach(ref c, ref bool remClause; &clauses.prune)
			{
				foreach(x, ref bool remLiteral; &c.prune)
				{
					if(assign[x])
					{
						remClause = true;
						change = true;
						continue outer;
					}

					if(assign[x^1])
						remLiteral = true;
				}

				if(c.length == 0)
					throw new Exception("answer is UNSAT (FIXME/TODO)");

				if(c.length == 1)
				{
					assign[c[0]] = true;
					remClause = true;
					change = true;
					continue outer;
				}
			}

			if(!change)
				break;
		}

		clauses.makeSet();
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
		writefln("solving %s: v=%s c=%s", name[max(0,cast(int)$-50)..$], varCount, clauses.length);

		cleanup();	// actually not worth it on my testcases, but not by much
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

			test();
		}
		else
			throw new Exception("answer is UNSAT (might be correct, but needs cheking)");
	}
}
