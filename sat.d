module sat;

import std.stdio;
import std.conv;
import jive.array;
private import std.algorithm : move;
import solver, clause;
import std.parallelism;


class Sat
{
	const string name;
	Array!(Array!int) clauses;
	Array!bool assign;
	int varCount;
	Array!(Array!int) occs;
	Array!bool blocked;

	void test()
	{
		for(int x = 0; x < 2*varCount; x+=2)
		{
			if(!assign[x] && !assign[x^1])
				throw new Exception("incomplete assignment on variable "~to!string(x));

			if(assign[x] && assign[x^1])
				throw new Exception("invalid assignment");
		}

		outer: foreach(ref c; clauses)
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
		blocked.reserve(clauseCount);
		assign.resize(2*varCount);
		occs.resize(2*varCount);

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
			blocked.pushBack(false);
		}
	}

	void solve()
	{
		writefln("solving %s: v=%s c=%s", name[25..$], varCount, clauses.length);

		auto renum = new int[2*varCount];
		renum[] = -1;
		{
			int i = 0;
			for(int x = 0; x < 2*varCount; x+=2)
				if(!assign[x] && !assign[x^1])
				{
					renum[x] = i;
					renum[x^1] = i^1;
					i += 2;
				}
		}

		auto db = new ClauseDB(varCount);
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
