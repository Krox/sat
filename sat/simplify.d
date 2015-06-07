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
				subsume(i);
		sat.propagate();
		swSubsume.stop();
	}

	/** perform subsumption and self-subsuming resolution using implications a -> * (also find failed literals) */
	private void binarySubsume(Lit a)
	{
		assert(sat.prop.empty);

		if(sat.renum[a.var] == -1)
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
	private void subsume(int k)
	{
		assert(sat.prop.empty);

		Lit[] c = sat.clauses[k][];
		Lit pivot = c[0];
		foreach(l; c[1..$])
			if(sat.occCount(l)+sat.occCount(l.neg) < sat.occCount(pivot)+sat.occCount(pivot.neg))
				pivot = l;
		foreach(j; sat.occs(pivot))
			strengthen(j, k);
		foreach(j; sat.occs(pivot.neg))
			strengthen(j, k);
	}

	/** strengthen i using k */
	private void strengthen(int i, int k)
	{
		if(i == k)
			return;

		Lit rem = Lit.undef;

		Lit[] a = sat.clauses[i][];
		Lit[] b = sat.clauses[k][];

		while(b.length) // modified subset algorithm
		{
			if(a.length < b.length)
				return;
			else if(a.front == b.front)
			{
				a.popFront;
				b.popFront;
			}
			else if(a.front == b.front.neg)
			{
				if(rem != Lit.undef)
					return;
				rem = a.front;
				a.popFront;
				b.popFront;
			}
			else
				a.popFront;
		}

		if(rem is Lit.undef) // subsumed without any flip -> remove clause i
		{
			if(sat.clauses[i].irred) // if k subsumes an irreducible clause, k itself becomes irreducible
				sat.makeClauseIrred(k);
			++nRemovedCls;
			sat.removeClause(i);
		}
		else // subsumed with exactly one flip -> strengthen clause i
		{
			sat.removeLiteral(i, rem);
			++nRemovedLits;
		}
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
	}
}
