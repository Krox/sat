module sat.simplify;

import std.stdio;
import std.range;

import jive.array;
import jive.lazyarray;

import sat.sat;
import sat.stats;

/** subsumption and self-subsuming resolution */
class simplify
{
	Sat sat;

	private LazyBitArray seen;
	private Array!Lit stack;

	// some statistics
	int nRemovedCls; // clauses removed by subsumption
	int nRemovedClsBin; // clauses removed by subsumption
	int nRemovedLits; // clauses strengthened by self-subsuming resolution
	int nRemovedLitsBin; // clauses strengthened by self-subsuming resolution
	int nFailedLits;
	long nImplications; // number if implications in the binary problem
	int nLitsWithImplications;

	void run()
	{
		swSubsumeBinary.start();
		for(int i = 0; i < sat.varCount*2; ++i)
			binarySubsume(Lit(i));
		sat.propagate();
		swSubsumeBinary.stop();

		swSubsume.start();
		foreach(int i, ref c; sat.clauses)
			if(c.length)
				subsume(i, sat.clauses[i]);
		sat.propagate();
		swSubsume.stop();
	}

	/** perform subsumption and self-subsuming resolution using implications a -> * (also find failed literals) */
	private void binarySubsume(Lit a)
	{
		assert(sat.prop.empty);

		if(sat.assign.valueInner(a) != Lit.undef)
			return;

		if(sat.bins(a.neg).length == 0) // early-out for literals without any implications
			return;

		++nLitsWithImplications;

		// mark all literals reachable from a
		seen.reset();
		assert(stack.empty);
		stack.pushBack(a);
		seen[a] = true;
		while(!stack.empty)
			foreach(b; sat.bins(stack.popBack().neg))
				if(!seen[b])
				{
					seen[b] = true;
					stack.pushBack(b);
					++nImplications;
				}
		seen[a] = false;

		// if !a is reachable, a is a failed literal
		if(seen[a.neg])
		{
			sat.addUnary(a.neg);
			sat.propagate();
			++nFailedLits;
			return;
		}

		// remove clauses subsumed by some implication a -> *
		foreach(k; sat.occs(a.neg))
			foreach(x; sat.clauses[k])
				if(seen[x])
				{
					sat.removeClause(k);
					++nRemovedClsBin;
					break;
				}

		// strengthen clauses using implications a -> *
		foreach(k; sat.occs(a))
			foreach(x; sat.clauses[k])
				if(seen[x])
				{
					sat.removeLiteral(k, a);
					++nRemovedLitsBin;
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
			++nRemovedCls;
			sat.removeClause(j);
		}

		assert(sat.prop.empty);

		for(int i = 0; i < c.length; ++i)
		{
			c[i] = c[i].neg;
			foreach(j; findSubsumed(c))
			{
				sat.removeLiteral(j, c[i]);
				++nRemovedLits;
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
		writefln("c simplify used %s implications from %s lits (%.1f %%)", x.nImplications, x.nLitsWithImplications, x.nLitsWithImplications/(2.0*sat.varCount)*100);
		writefln("c simplify removed %s+%s cls, %s+%s lits and %s failed literals", x.nRemovedClsBin, x.nRemovedCls, x.nRemovedLitsBin, x.nRemovedLits, x.nFailedLits);
	}
}
