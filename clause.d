module clause;

import jive.array;
private import std.algorithm : move, swap;

final class ClauseDB
{
	const int varCount;	// note: making this unsigned will/has/might lead to bugs

	static struct pair { int a,b; }
	Array!(Array!pair) clausesTri;

	Array!(Array!int) clausesLong;
	Array!(Array!int) occsLong;

	Array!bool assign;
	Array!int stack;

	this(int varCount)
	{
		this.varCount = varCount;
		this.clausesTri.resize(2*varCount);
		this.occsLong.resize(2*varCount);
		stack.reserve(varCount);
		assign.resize(2*varCount);
	}

	void addClause(int[] c)	// NOTE: makes copy of the clause
	{
		switch(c.length)
		{
			case 0:
			case 1:
				throw new Exception("invalid clause length in solver");

			case 2:
				throw new Exception("TODO / FIXME");

			case 3:
				clausesTri[c[0]].pushBack(pair(c[1],c[2]));
				clausesTri[c[1]].pushBack(pair(c[0],c[2]));
				clausesTri[c[2]].pushBack(pair(c[0],c[1]));
				break;

			default:
				assert(c.length >= 4);
				foreach(x; c)
					occsLong[x].pushBack(cast(int)clausesLong.length);
				clausesLong.pushBack(Array!int(c[]));
				break;
		}
	}

	void set(int x)
	{
		assign[x] = true;
		stack.pushBack(x);
	}

	int propagate(int _x)	// returns number of set variables. 0 on conflict.
	{
		size_t pos = stack.length;
		size_t startpos = pos;

		set(_x);

		while(pos != stack.length)
		{
			auto x = stack[pos++];

			foreach(pair c; clausesTri[x^1])
			{
				if(assign[c.a] || assign[c.b])	// clause satisfied -> do nothing
					continue;

				if(assign[c.a^1])
					if(assign[c.b^1])
					{
						while(stack.length != startpos)
							assign[stack.popBack] = false;
						return 0;
					}
					else
						set(c.b);
				else
					if(assign[c.b^1])
						set(c.a);
					else
						continue;
			}

			outer: foreach(i; occsLong[x^1])
			{
				int[] c = clausesLong[i][];

				int unit = -1;
				foreach(y; c)
				{
					if(assign[y])
						continue outer;	// clause satisfied -> do nothing

					if(assign[y^1])
						continue;

					if(unit != -1)
						continue outer;	// clause not unit (might also be satisfied) -> do nothing

					unit = y;
				}

				if(unit == -1) // clause all false -> conflict
				{
					while(stack.length != startpos)
						assign[stack.popBack] = false;
					return 0;
				}

				set(unit);
			}
		}

		return cast(int)(pos - startpos);
	}

	void unroll(int x)
	{
		while(true)
		{
			int y = stack.popBack;
			//assert(assign[y]);
			assign[y] = false;
			if(y == x)
				break;
		}
	}
}














