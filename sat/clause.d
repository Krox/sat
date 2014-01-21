module sat.clause;

import jive.array;
private import std.algorithm : move, swap;
import sat.sat;

final class ClauseDB
{
	const int varCount;	// note: making this unsigned will/has/might lead to bugs
	int clauseCount;

	Array!(Array!Lit) clausesBin;

	static struct pair { Lit a,b; }
	Array!(Array!pair) clausesTri;

	Array!(Array!Lit) clausesLong;	// no need for sorting, so don't use Clause
	Array!(Array!int) occsLong;

	Array!bool assign;
	Array!Lit stack;

	this(int varCount)
	{
		assert(varCount > 0);

		this.varCount = varCount;
		this.clausesBin.resize(2*varCount);
		this.clausesTri.resize(2*varCount);
		this.occsLong.resize(2*varCount);
		stack.reserve(varCount);
		assign.resize(2*varCount);
	}

	void addClause(Lit[] c)	// NOTE: makes copy of clause (if applicable, as short clauses are implicit)
	{
		++clauseCount;

		switch(c.length)
		{
			case 0:
			case 1:
				throw new Exception("invalid clause length in solver");

			case 2:
				clausesBin[c[0]].pushBack(c[1]);
				clausesBin[c[1]].pushBack(c[0]);
				break;

			case 3:
				clausesTri[c[0]].pushBack(pair(c[1],c[2]));
				clausesTri[c[1]].pushBack(pair(c[0],c[2]));
				clausesTri[c[2]].pushBack(pair(c[0],c[1]));
				break;

			default:
				assert(c.length >= 4);
				foreach(x; c)
					occsLong[x].pushBack(cast(int)clausesLong.length);
				clausesLong.pushBack(Array!Lit(c));
				break;
		}
	}

	void set(Lit x)
	{
		assign[x] = true;
		stack.pushBack(x);
	}

	/** sets one literal, and performs unit propagation
	    returns slice of newly set variable
	    returns empty non-null if literal was already set
	    returns null on conflict (state unchanged in this case) **/
	Lit[] propagate(Lit _x)
	{
		if(assign[_x])
			return stack[$..$];	// note this is not null

		if(assign[_x.neg])
			return null;

		size_t pos = stack.length;
		size_t startpos = pos;

		set(_x);

		while(pos != stack.length)
		{
			auto x = stack[pos++];

			foreach(Lit y; clausesBin[x.neg])
			{
				if(assign[y])
					continue;

				if(assign[y^1])
				{
					while(stack.length != startpos)
						assign[stack.popBack] = false;
					return null;
				}

				set(y);
			}

			foreach(pair c; clausesTri[x.neg])
			{
				if(assign[c.a] || assign[c.b])	// clause satisfied -> do nothing
					continue;

				if(assign[c.a.neg])
					if(assign[c.b.neg])
					{
						while(stack.length != startpos)
							assign[stack.popBack] = false;
						return null;
					}
					else
						set(c.b);
				else
					if(assign[c.b.neg])
						set(c.a);
					else
						continue;
			}

			outer: foreach(i; occsLong[x.neg])
			{
				Lit unit = Lit.nil;

				foreach(y; clausesLong[i])
				{
					if(assign[y])
						continue outer;	// clause satisfied -> do nothing

					if(assign[y.neg])
						continue;

					if(unit != Lit.nil)
						continue outer;	// clause not unit (might also be satisfied) -> do nothing

					unit = y;
				}

				if(unit == Lit.nil) // clause all false -> conflict
				{
					while(stack.length != startpos)
						assign[stack.popBack] = false;
					return null;
				}

				set(unit);
			}
		}

		return stack[startpos..$];
	}

	void unroll(Lit x)
	{
		while(true)
		{
			Lit y = stack.popBack;
			//assert(assign[y]);
			assign[y] = false;
			if(y == x)
				break;
		}
	}
}














