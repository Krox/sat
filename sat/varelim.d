module sat.varelim;

import std.stdio;
import std.range;

import jive.array;
import jive.bitarray;
import jive.segmenttree;

import sat.sat;
import sat.stats;

/** bounded variable elimination */
class varElim
{
	Sat sat;
	PriorityArray!int score; // the lower the better (only negative ones are actually realized)

	int nRemovedVariables; // variables eliminated by resolution

	private BitArray seen;
	private Array!int todo;

	private void run()
	{
		while(score.min < 0)
		{
			int i = cast(int)score.minIndex;

			// determine other variables whose score will have to be recalculated
			foreach(x; sat.bins(Lit(i, false)))
				if(seen.add(x.var))
					todo.pushBack(x.var);
			foreach(x; sat.bins(Lit(i, true)))
				if(seen.add(x.var))
					todo.pushBack(x.var);
			foreach(k; sat.occs(Lit(i, false)))
				if(sat.clauses[k].irred)
					foreach(x; sat.clauses[k])
						if(seen.add(x.var))
							todo.pushBack(x.var);
			foreach(k; sat.occs(Lit(i, true)))
				if(sat.clauses[k].irred)
					foreach(x; sat.clauses[k])
						if(seen.add(x.var))
							todo.pushBack(x.var);

			// eliminate the variable
			++nRemovedVariables;
			eliminate(i);
			sat.propagate(); // there wont usually be anything to be propagated (as long as flp and stuff was already done)

			// recalculate scores of affected variable
			score[i] = 1000;
			foreach(j; todo)
			{
				seen[j] = false;
				score[j] = calcScore(sat, j);
			}

			todo.resize(0);
		}
	}

	private this(Sat sat)
	{
		this.sat = sat;
		seen = BitArray(sat.varCount);
		score = PriorityArray!int(sat.varCount);
		for(int i = 0; i < sat.varCount; ++i)
			score[i] = calcScore(sat, i);
	}

	static void opCall(Sat sat)
	{
		swVarElim.start();
		auto x = new varElim(sat);
		x.run();
		swVarElim.stop();
	}

	/**
	 * Calculate the score of removing variable v, the lower the better.
	 * Returns (arbitrary) positive number if its not worth doing.
	 */
	private static int calcScore(Sat sat, int v)
	{
		if(sat.renum[v] == -1)
			return 1000;

		auto pos = Lit(v, false);
		auto neg = Lit(v, true);

		if(sat.occCountIrred[pos] + sat.bins(pos).length > 10 // its not worth scoring variables with many occurences
			&& sat.occCountIrred[neg] + sat.bins(neg).length > 10)
			return 1000;

		int score = 0; // NOTE: only count the difference in irreducible clauses (which includes all binaries)
		score -= sat.occCountIrred[pos];
		score -= sat.occCountIrred[neg];
		score -= cast(int)sat.bins(pos).length;
		score -= cast(int)sat.bins(neg).length;

		// binary-binary
		// NOTE: these can not result in tautologies (or units) as
		//       long as flp and tarjan were performed before
		score += cast(int)(sat.bins(pos).length*sat.bins(neg).length);

		// long-binary
		foreach(i; sat.occs(pos))
			if(sat.clauses[i].irred)
				foreach(x; sat.bins(neg))
					if(x.neg !in sat.clauses[i])
						if(++score > 0)
							return 1000;
		foreach(i; sat.occs(neg))
			if(sat.clauses[i].irred)
				foreach(x; sat.bins(pos))
					if(x.neg !in sat.clauses[i])
						if(++score > 0)
							return 1000;

		// long-long
		foreach(i; sat.occs(pos))
			if(sat.clauses[i].irred)
				foreach(j; sat.occs(neg))
					if(sat.clauses[j].irred)
						if(!isResolventTautological(sat.clauses[i], sat.clauses[j]))
							if(++score > 0)
								return 1000;

		return score;
	}

	/** resolvent of a with b using the pivot l */
	static Lit[] resolvent(const Lit[] a, const Lit[] b, Lit l)
	{
		Array!Lit c;
		c.resize(0);
		c.pushBack(a);
		c.pushBack(b);
		sort(c[]);

		Lit last = Lit.undef;
		foreach(lit, ref bool rem; &c.prune)
		{
			if(lit == last || lit == l || lit == l.neg)
				rem = true;
			else if(lit == last.neg)
				return null;
			else
				last = lit;
		}

		return c[];
	}

	/** resolvent of a with the binary clause b,l using the pivot l */
	static Lit[] resolvent(const Lit[] a, Lit b, Lit l)
	{
		Array!Lit c;
		c.resize(0);
		c.pushBack(a);
		bool found = false;
		for(int i = 0; i < c.length; ++i)
		{
			if(c[i] == b.neg)
				return null;
			else if(c[i] == l.neg)
			{
				assert(!found);
				found = true;
				c[i] = b;
			}
			else if(c[i] == b)
			{
				c[i] = c[$-1];
				c.popBack();
				--i;
			}
		}
		assert(found);

		return c[];
	}

	/** check whether a resolvent is tautological without actually computing it */
	static bool isResolventTautological(const ref Clause a, const ref Clause b)
	{
		int r = 0;
		foreach(x; a[])
			foreach(y; b[])
				if(x == y.neg)
					if(++r >= 2)
						return true;
		return false;
	}

	void eliminate(int v)
	{
		assert(sat.renum[v] != -1);

		auto pos = Lit(v, false);
		auto neg = Lit(v, true);

		// add binary-binary resolvents
		foreach(x; sat.bins(pos))
			foreach(y; sat.bins(neg))
				sat.addBinary(x, y);
		foreach(x; sat.bins(neg))
			foreach(y; sat.bins(pos))
				sat.addBinary(x, y);

		// add long-binary resolvents
		foreach(i; sat.occs(pos))
			if(sat.clauses[i].irred)
				foreach(x; sat.bins(neg))
					if(x.neg !in sat.clauses[i])
					{
						auto r = resolvent(sat.clauses[i][], x, neg);
						if(r !is null)
							sat.addClause(r, true);
					}
		foreach(i; sat.occs(neg))
			if(sat.clauses[i].irred)
				foreach(x; sat.bins(pos))
					if(x.neg !in sat.clauses[i])
					{
						auto r = resolvent(sat.clauses[i][], x, pos);
						if(r !is null)
							sat.addClause(r, true);
					}

		// add long-long resolvents
		foreach(i; sat.occs(pos))
			if(sat.clauses[i].irred)
				foreach(j; sat.occs(neg))
					if(sat.clauses[j].irred)
					{
						auto r = resolvent(sat.clauses[i][], sat.clauses[j][], pos);
						if(r !is null)
							sat.addClause(r, true);
					}

		auto ext = new Extender(sat.assign);

		// move old long clauses from the problem to the solution extender
		foreach(i; sat.occs(pos))
		{
			if(sat.clauses[i].irred)
				ext.clausesPos.pushBack(Array!Lit(sat.clauses[i][]));
			sat.removeClause(i);
		}
		foreach(i; sat.occs(neg))
		{
			if(sat.clauses[i].irred)
				ext.clausesNeg.pushBack(Array!Lit(sat.clauses[i][]));
			sat.removeClause(i);
		}

		// move old binary clauses from the problem to the solution extender
		ext.binsPos = move(sat.bins(pos));
		ext.binsNeg = move(sat.bins(neg));
		foreach(x; ext.binsPos)
			sat.binaryDirty[x] = true;
		foreach(x; ext.binsNeg)
			sat.binaryDirty[x] = true;

		// translate clauses to outer variable numbers
		v = sat.renum[v];
		foreach(ref c; ext.clausesPos)
			foreach(ref l; c)
				l = sat.toOuter(l);
		foreach(ref c; ext.clausesNeg)
			foreach(ref l; c)
				l = sat.toOuter(l);
		foreach(ref x; ext.binsPos)
			x = sat.toOuter(x);
		foreach(ref x; ext.binsNeg)
			x = sat.toOuter(x);

		sat.assign.eliminateVariable(v, &ext.eval);
		sat.varRemoved = true;
	}
}

final class Extender
{
	Assignment assign;
	Array!(Array!Lit) clausesPos; // clauses containing Lit(v, false)
	Array!(Array!Lit) clausesNeg; // clauses containing Lit(v, true)
	Array!Lit binsPos;
	Array!Lit binsNeg;

	this(Assignment assign)
	{
		this.assign = assign;
	}

	Lit eval()
	{
		bool needPos, needNeg;
		foreach(ref c; clausesPos)
			if(!assign.isSatisfied(c[]))
				{ needPos = true; break; }
		foreach(ref c; clausesNeg)
			if(!assign.isSatisfied(c[]))
				{ needNeg = true; break; }
		foreach(ref x; binsPos)
			if(assign[x] != Lit.one)
				{ needPos = true; break; }
		foreach(ref x; binsNeg)
			if(assign[x] != Lit.one)
				{ needNeg = true; break; }

		if(needPos && needNeg)
			throw new Exception("corrupt variable elimination");

		return Lit.zero^needPos;
	}
}
