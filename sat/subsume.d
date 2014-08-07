module sat.subsume;

import std.stdio;
import std.range;

import jive.array;

import sat.sat;

/** subsumption, self-subsuming resolution and bounded variable elimination */
class simplify
{
	Sat sat;

	int nRemovedClauses; // clauses removed by subsumption
	int nRemovedLiterals; // clauses strengthened by self-subsuming resolution
	int nRemovedVariables; // variables eliminated by resolution
	int nProp;

	void run()
	{
		foreach(int i, ref c; sat.clauses)
			if(c.length)
			{
				subsume(i);
				selfSubsume(c);
			}

		for(int i = 0; i < sat.varCount; ++i)
			if(maybeEliminate(i))
				++nRemovedVariables;
	}

	void subsume(int k)
	{
		foreach(j; findSubsumed(sat.clauses[k]))
		{
			//writefln("subsume %s <= %s", c[], sat.clauses[j][]);
			if(sat.clauses[j].irred) // if c subsumes an irreducible clause, c itself becomes irreducible
				sat.makeClauseIrred(k);
			++nRemovedClauses;
			sat.removeClause(j);
		}
		nProp += sat.propagate;
	}

	void selfSubsume(ref Clause c)
	{
		for(int i = 0; i < c.length; ++i)
		{
			c[i] = c[i].neg;
			foreach(j; findSubsumed(c))
			{
				sat.replaceOcc(j, c[i], Lit.zero);
				++nRemovedLiterals;
			}
			c[i] = c[i].neg;
		}
		nProp += sat.propagate;
	}

	auto findSubsumed(const ref Clause c)
	{
		static struct SubsumeList
		{
			Sat sat;
			const(Clause)* c;

			int opApply(int delegate(int) dg)
			{
				Lit best = (*c)[0];
				foreach(l; (*c)[1..$])
					if(sat.occCount(l) < sat.occCount(best))
						best = l;

				foreach(j; sat.occs(best))
					if(&sat.clauses[j] !is c && c.subset(sat.clauses[j]))
						if(int r = dg(j))
							return r;

				return 0;
			}
		}

		assert(c.length, "tried to subsume stuff with empty clause. probably not intended.");
		return SubsumeList(sat, &c);
	}

	static Clause resolvent(ref Clause a, ref Clause b, Lit l)
	{
		assert(a.irred && b.irred);
		auto c = Clause(a.amalgamation(b), true);
		if(!c.remove(l) || !c.remove(l.neg))
			assert(false);
		return c;
	}

	/** check whether a resolvent is tautological without actually computing it */
	static bool isResolventTautological(const ref Clause _a, const ref Clause _b)
	{
		int r = 0;
		auto a = _a[];
		auto b = _b[];

		while(a.length && b.length)
		{
			if(a.front.neg == b.front)
				{ ++r; a.popFront; b.popFront; }
			else if(a.front < b.front)
				a.popFront;
			else
				b.popFront;
		}

		assert(r >= 1);
		return r >= 2;
	}

	bool maybeEliminate(int v)
	{
		// dont eliminate variables that are fixed or already eliminated
		if(sat.assign.valueInner(Lit(v, false)) != Lit.undef)
			return false;

		int occPos = sat.occCountIrred[Lit(v, false)];
		int occNeg = sat.occCountIrred[Lit(v, true)];

		// heuristic cutoff for variables which are very unlikely to be worthwhile to eliminate
		if(occPos > 10 && occNeg > 10)
			return false;

		// check whether number of clauses would decrease upon elimination
		int score = occPos + occNeg;
		foreach(i; sat.occs(Lit(v, false)))
			if(sat.clauses[i].irred)
				foreach(j; sat.occs(Lit(v, true)))
					if(sat.clauses[j].irred)
						if(!isResolventTautological(sat.clauses[i], sat.clauses[j]))
							if(--score < 0)
								return false;

		eliminate(v);
		return true;
	}

	void eliminate(int v)
	{
		// add resolvents to the clause set
		foreach(i; sat.occs(Lit(v, false)))
			if(sat.clauses[i].irred)
				foreach(j; sat.occs(Lit(v, true)))
					if(sat.clauses[j].irred)
						sat.addClause(resolvent(sat.clauses[i], sat.clauses[j], Lit(v, false)), true); // 'addClause' will not add tautoligies

		// move old clauses from the problem to the solution extender
		auto ext = new Extender(sat.assign);
		foreach(i; sat.occs(Lit(v, false)))
			ext.clausesPos.pushBack(sat.removeClause(i)); // TODO: skip reducible
		foreach(i; sat.occs(Lit(v, true)))
			ext.clausesNeg.pushBack(sat.removeClause(i));

		// translate clauses to outer variable numbers
		v = sat.assign.toOuter(Lit(v,false)).var;
		foreach(ref c; ext.clausesPos)
			foreach(ref l; c)
				l = sat.assign.toOuter(l);
		foreach(ref c; ext.clausesNeg)
			foreach(ref l; c)
				l = sat.assign.toOuter(l);

		sat.assign.eliminateVariableOuter(v, &ext.eval);
		sat.varRemoved = true;
		nProp += sat.propagate();
		//assert(sat.prop.empty);
	}

	private this(Sat sat)
	{
		this.sat = sat;
	}

	static void opCall(Sat sat)
	{
		auto x = new simplify(sat);
		x.run();
		writefln("c simplify removed %s cls, %s lits, %s vars and propagated %s", x.nRemovedClauses, x.nRemovedLiterals, x.nRemovedVariables, x.nProp);
	}
}

static class Extender
{
	Assignment assign;
	Array!Clause clausesPos; // clauses containing Lit(v, false)
	Array!Clause clausesNeg; // clauses containing Lit(v, true)

	this(Assignment assign)
	{
		this.assign = assign;
	}

	Lit eval(int v)
	{
		bool needPos, needNeg;
		foreach(ref c; clausesPos)
			if(!assign.isSatisfiedOuter(c[]))
				{ needPos = true; break; }
		foreach(ref c; clausesNeg)
			if(!assign.isSatisfiedOuter(c[]))
				{ needNeg = true; break; }

		if(needPos && needNeg)
			throw new Exception("corrupt variable elimination");

		return Lit.zero^needPos;
	}
}
