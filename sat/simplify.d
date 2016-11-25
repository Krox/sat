module sat.simplify;

import std.stdio;
import std.range;

import jive.array;
import jive.bitarray;

import sat.sat;
import sat.stats;

/** subsumption and self-subsuming resolution */
class simplify
{
	Sat sat;

	private BitArray seen;
	private Array!Lit stack;
	private Array!(Array!CRef) occs;

	// some statistics
	int nRemovedClsBin; // clauses removed by subsumption
	int nRemovedLitsBin; // clauses strengthened by self-subsuming resolution
	int nFailedLits;
	long nImplications; // number of implications in the binary problem
	int nLitsWithImplications;

	void run()
	{
		swSubsumeBinary.start();

		seen = BitArray(sat.varCount*2); // TODO: decide between lazy/normal

		occs.resize(0);
		occs.resize(sat.varCount*2);
		foreach(k, ref c; sat.clauses)
			foreach(Lit x; c)
				occs[x].pushBack(k);

		for(int i = 0; i < sat.varCount*2; ++i)
			binarySubsume(Lit(i));

		swSubsumeBinary.stop();
	}

	/** perform subsumption and self-subsuming resolution using implications a -> * (also find failed literals) */
	private void binarySubsume(Lit a)
	{
		// early-out for literals without any implications
		if(sat.bins[a.neg].length == 0)
			return;
		++nLitsWithImplications;

		// mark all literals reachable from a
		seen.reset();
		assert(stack.empty);
		stack.pushBack(a);
		seen[a] = true;
		while(!stack.empty)
			foreach(b; sat.bins[stack.popBack().neg])
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
			sat.addClause(a.neg);
			++nFailedLits;
			return;
		}

		// remove clauses subsumed by some implication a -> *
		foreach(k; occs[a.neg])
			if(!sat.clauses[k].removed) // happens if subsumed by multiple (hyper-)binary clauses
				foreach(x; sat.clauses[k])
					if(seen[x])
					{
						sat.clauses[k].remove();
						++nRemovedClsBin;
						break;
					}

		// strengthen clauses using implications a -> *
		foreach(k; occs[a])
			if(!sat.clauses[k].removed)
				foreach(x; sat.clauses[k])
					if(seen[x])
					{
						sat.clauses[k].removeLiteral(a);
						++nRemovedLitsBin;
						break;
					}
	}

	private this(Sat sat)
	{
		this.sat = sat;
	}

	static void opCall(Sat sat)
	{
		auto x = new simplify(sat);
		x.run();
	}
}
