module sat.simplify;

import std.stdio;
import std.range;

import jive.array;
import jive.lazyarray;

import sat.sat;

/** subsumption and self-subsuming resolution */
class simplify
{
	Sat sat;

	private LazyBitArray seen;
	private Array!Lit stack;

	int nRemovedClauses; // clauses removed by subsumption
	int nRemovedClausesBin; // clauses removed by subsumption
	int nRemovedLiterals; // clauses strengthened by self-subsuming resolution
	int nRemovedLiteralsBin; // clauses strengthened by self-subsuming resolution
	int nFailedLiterals;

	void run()
	{
		for(int i = 0; i < sat.varCount*2; ++i)
			binarySubsume(Lit(i));

		foreach(int i, ref c; sat.clauses)
			if(c.length)
				subsume(i, sat.clauses[i]);

		sat.propagate();
	}

	/** perform subsumption and self-subsuming resolution using implications a -> * (also find failed literals) */
	private void binarySubsume(Lit a)
	{
		assert(sat.prop.empty);

		if(sat.assign.valueInner(a) != Lit.undef)
			return;

		// mark all literals reachable from a
		seen.reset();
		assert(stack.empty);
		stack.pushBack(a);
		while(!stack.empty)
			foreach(b; sat.bins(stack.popBack().neg))
				if(!seen[b])
				{
					seen[b] = true;
					stack.pushBack(b);
				}
		seen[a] = false; // in case of equivalent literals, a could have been set.

		// if !a is reachable, a is a failed literal
		if(seen[a.neg])
		{
			sat.addUnary(a.neg);
			sat.propagate();
			++nFailedLiterals;
			return;
		}

		// remove clauses subsumed by some implication a -> *
		foreach(k; sat.occs(a.neg))
			foreach(x; sat.clauses[k])
				if(seen[x])
				{
					sat.removeClause(k);
					++nRemovedClausesBin;
					break;
				}

		// strengthen clauses using implications a -> *
		foreach(k; sat.occs(a))
			foreach(x; sat.clauses[k])
				if(seen[x])
				{
					sat.removeLiteral(k, a);
					++nRemovedLiteralsBin;
					break;
				}

		assert(sat.prop.empty()); // removing clauses and strengthening long clauses cannot result in units
	}

	/** remove all clauses subsumed by and strengthen all clauses using clause k */
	private void subsume(int k, ref Clause c)
	{
		foreach(j; findSubsumed(c))
		{
			if(sat.clauses[j].irred) // if c subsumes an irreducible clause, c itself becomes irreducible
				sat.makeClauseIrred(k);
			++nRemovedClauses;
			sat.removeClause(j);
		}

		assert(sat.prop.empty);

		for(int i = 0; i < c.length; ++i)
		{
			c[i] = c[i].neg;
			foreach(j; findSubsumed(c))
			{
				sat.removeLiteral(j, c[i]);
				++nRemovedLiterals;
			}
			c[i] = c[i].neg;
		}

		assert(sat.prop.empty);
	}

	/* returns range of all clauses subsumed by c */
	private auto findSubsumed(const ref Clause c)
	{
		static struct SubsumeList
		{
			Sat sat;
			const(Clause)* c;

			int opApply(int delegate(int) dg)
			{
				/* find literal with shortes occurence list */
				Lit best = (*c)[0];
				foreach(l; (*c)[1..$])
					if(sat.occCount(l) < sat.occCount(best))
						best = l;

				/* check all occurences of that literal for subsumption */ // TODO: use a bloom filter to speed this up
				foreach(j; sat.occs(best))
					if(&sat.clauses[j] !is c) // a clause may not subsume itself
						 if(c.subset(sat.clauses[j]))
							if(int r = dg(j))
								return r;

				return 0;
			}
		}

		assert(c.length, "tried to subsume stuff with empty clause. probably not intended.");
		return SubsumeList(sat, &c);
	}

	private this(Sat sat)
	{
		this.sat = sat;
		seen.resize(sat.varCount*2);
	}

	static void opCall(Sat sat)
	{
		auto x = new simplify(sat);
		x.run();
		writefln("c simplify removed %s+%s cls, %s+%s lits and %s failed literals", x.nRemovedClausesBin, x.nRemovedClauses, x.nRemovedLiteralsBin, x.nRemovedLiterals, x.nFailedLiterals);
	}
}
