module sat.clause;

import jive.array;
import jive.lazyarray;
private import std.algorithm : move, swap;
import std.stdio;
import sat.sat;

struct Reason
{
	enum
	{
		nil,
		unary,
		binary,
		ternary,
		clause
	}

	int type;
	union { Lit lit2; int n; }
	Lit lit3;

	static enum Reason descision = make(nil);
	static enum Reason unit = make(unary);

	static Reason make(int type)
	{
		Reason r;
		r.type = type;
		return r;
	}

	this(Lit lit2)
	{
		this.type = binary;
		this.lit2 = lit2;
	}

	this(Lit lit2, Lit lit3)
	{
		this.type = ternary;
		this.lit2 = lit2;
		this.lit3 = lit3;
	}

	this(int n)
	{
		this.type = clause;
		this.n = n;
	}
}

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
	Array!int level; // only valid for assigned variables
	Array!int savePoint; // indices into stack
	int currLevel() const @property { return cast(int) savePoint.length; }

	Array!Reason reason;
	Lit[] conflict;
	Lit[3] _conflict;
	private LazyBitArray seen;

	this(int varCount)
	{
		assert(varCount > 0);

		this.varCount = varCount;
		this.clausesBin.resize(2*varCount);
		this.clausesTri.resize(2*varCount);
		this.occsLong.resize(2*varCount);
		stack.reserve(varCount);
		level.resize(varCount);
		assign.resize(2*varCount);
		reason.resize(varCount);
		seen.resize(varCount);
	}

	/**
	 * add a new clause
	 *    - makes copy of the argument (if applicable, as short clauses are implicit)
	 *    - does not immediately propagate using the new clause
	 *    - returns reason appropriate for setting c[0] using the new clause
	 */
	Reason addClause(Lit[] c)
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
				return Reason(c[1]);

			case 3:
				clausesTri[c[0]].pushBack(pair(c[1], c[2]));
				clausesTri[c[1]].pushBack(pair(c[0], c[2]));
				clausesTri[c[2]].pushBack(pair(c[0], c[1]));
				return Reason(c[1], c[2]);

			default:
				assert(c.length >= 4);
				int i = cast(int)clausesLong.length;
				foreach(x; c)
					occsLong[x].pushBack(i);
				clausesLong.pushBack(Array!Lit(c));
				return Reason(i);
		}
	}

	void bumpLevel()
	{
		savePoint.pushBack(cast(int)stack.length);
	}

	void set(Lit x, Reason r)
	{
		//assert(!assign[x] && !assign[x.neg]);
		assign[x] = true;
		stack.pushBack(x);
		level[x.var] = currLevel;
		reason[x.var] = r;
	}

	/**
	 * set one literal and performs unit propagation
	 * returns slice of newly assigned variables
	 * returns empty non-null if literal was already set
	 * returns null on conflict (and set conflict)
	 **/
	Lit[] propagate(Lit _x, Reason reason)
	{
		if(reason == Reason.descision)
			assert(currLevel > 0);

		if(assign[_x])
			return stack[$..$];	// note this is not null

		if(assign[_x.neg])
			return null;

		size_t pos = stack.length;
		size_t startpos = pos;

		set(_x, reason);

		while(pos != stack.length)
		{
			auto x = stack[pos++];

			foreach(Lit y; clausesBin[x.neg])
			{
				if(assign[y])
					continue;

				if(assign[y.neg])
				{
					_conflict[0] = x.neg;
					_conflict[1] = y;
					conflict = _conflict[0..2];
					return null;
				}

				set(y, Reason(x.neg));
			}

			foreach(pair c; clausesTri[x.neg])
			{
				if(assign[c.a] || assign[c.b])	// clause satisfied -> do nothing
					continue;

				if(assign[c.a.neg])
					if(assign[c.b.neg])
					{
						_conflict[0] = x.neg;
						_conflict[1] = c.a;
						_conflict[2] = c.b;
						conflict = _conflict[0..3];
						return null;
					}
					else
						set(c.b, Reason(x.neg, c.a));
				else
					if(assign[c.b.neg])
						set(c.a, Reason(x.neg, c.b));
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
					conflict = clausesLong[i][0..$];
					return null;
				}

				set(unit, Reason(i));
			}
		}

		return stack[startpos..$];
	}

	/**
	 * returns learnt clause as slice into a temporary buffer.
	 * clause[0] is the asserting literal.
	 * clause[1] has the highest level (if clause.length >= 2).
	 */
	Lit[] analyzeConflict()
	{
		assert(conflict !is null, "no conflict here to be analyzed");
		assert(currLevel > 0, "analyzing a conflict on level 0 does not make sense");

		seen.reset();
		static Array!Lit buf;
		buf.resize(1); // room for the asserting literal itself

		int count = 0;

		void visit(Lit lit)
		{
			if(seen[lit.var] || level[lit.var] == 0) // level 0 assignments are definite, so these variables can be skipped
				return;
			seen[lit.var] = true;

			if(level[lit.var] < currLevel) // reason side
				buf.pushBack(lit);
			else // conflict side (includes the UIP itself)
				count++;
		}

		foreach(lit; conflict)
			visit(lit);

		int i = cast(int)stack.length;
		while(true)
		{
			--i;
			if(!seen[stack[i].var])
				continue;

			if(--count == 0)
				break;

			switch(reason[stack[i].var].type)
			{
				case Reason.unary:
					break;

				case Reason.binary:
					visit(reason[stack[i].var].lit2);
					break;

				case Reason.ternary:
					visit(reason[stack[i].var].lit2);
					visit(reason[stack[i].var].lit3);
					break;

				case Reason.clause:
					foreach(lit; clausesLong[reason[stack[i].var].n])
						if(lit.var != stack[i].var)
							visit(lit);
					break;

				default:
					throw new Exception("invalid reason type in conflict analysis");
			}
		}

		buf[0] = stack[i].neg;

		if(buf.length > 1)
		{
			int m = 1;
			for(int k = 2; k < buf.length; ++k)
				if(level[buf[k].var] > level[buf[m].var])
					m = k;
			swap(buf[1], buf[m]);
		}

		conflict = null;
		return buf[];
	}

	/** unroll all assignments in current level, but stay at current level */
	void unrollCurrLevel()
	{
		assert(currLevel > 0);
		while(stack.length > savePoint[$-1])
			assign[stack.popBack] = false;
	}

	/** unroll all assignments in levels > l, and set level to l */
	void unrollLevel(int l)
	{
		assert(l < currLevel);
		while(stack.length > savePoint[l])
			assign[stack.popBack] = false;
		savePoint.resize(l);
	}
}
