module sat.solver;

import std.stdio;
import std.datetime : Clock;

import jive.array;
import jive.lazyarray;

import sat.sat;
import sat.propengine;
import sat.stats;

final class Solver
{
	PropEngine engine;
	Sat sat;
	LazyBitArray blocked;
	Lit probe = Lit(0, false);

	long nProbes;
	long nFails;

	this(Sat sat)
	{
		this.sat = sat;
		blocked.resize(sat.varCount*2);

		engine = new PropEngine(sat);
	}

	bool failedLiteralProbing(ref Lit branch)
	{
		int bestScore = -1;
		branch = Lit.undef;

		engine.bumpLevel();
		blocked.reset();

		auto stop = probe;

		do // TODO: do in in non-arbitrary order to better exploit dominating literals
		{
			if(!engine.assign[probe] && !engine.assign[probe.neg] && !blocked[probe])
			{
				++nProbes;
				auto r = engine.propagate(probe, Reason.descision);

				if(r is null) // there was a conflict
				{
					++nFails;
					return false;
				}

				foreach(x; r[1..$])
					blocked[x] = true;

				int score = cast(int)r.length;
				engine.unrollCurrLevel();

				if(score > bestScore)
				{
					bestScore = score;
					branch = probe;
				}
			}
			probe.toInt = (probe.toInt+1)%(sat.varCount*2);
		}
		while(probe != stop);

		return true;
	}

	/** throws on UNSAT */
	void solveSome(int numConflicts)
	{
		size_t binCount = 0;
		for(int i = 0; i < sat.varCount*2; ++i)
			binCount += sat.bins(Lit(i)).length;
		binCount /= 2;

		writefln("c start solver with %s vars and %s / %s / %s clauses", engine.varCount, binCount, engine.clauseCountTernary, engine.clauseCountLong);

		while(true)
		{
			int branch = engine.mostActiveVariable;

			if(branch == -1)
			{
				for(int v = 0; v < engine.varCount; ++v)
				{
					if(engine.assign[Lit(v, false)])
						sat.addUnary(Lit(v, false));
					else if(engine.assign[Lit(v, true)])
						sat.addUnary(Lit(v, true));
					else assert(false);
				}

				return;
			}

			engine.bumpLevel();
			if(engine.propagate(Lit(branch, false), Reason.descision) is null)
			{
				handleConflict:

				if(numConflicts-- == 0)
					return;

				auto conflictClause = engine.analyzeConflict();
				sat.addClause(Array!Lit(conflictClause), false);

				if(engine.currLevel == 0) // conflict on level 0 -> UNSAT
					throw new Unsat;

				//writefln("conflict: %s", conflictClause[]);

				if(conflictClause.length == 1)
				{
					engine.unrollLevel(0);
					if(engine.propagate(conflictClause[0], Reason.unit) is null)
						throw new Unsat;
				}
				else if(conflictClause.length == 2)
				{
					// NOTE: don't add the clause to db explicitly
					engine.unrollLevel(engine.level[conflictClause[1].var]);
					if(engine.propagate(conflictClause[0], Reason(conflictClause[1])) is null)
						goto handleConflict;
				}
				else
				{
					engine.unrollLevel(engine.level[conflictClause[1].var]);
					auto reason = engine.addClause(conflictClause);
					if(engine.propagate(conflictClause[0], reason) is null)
						goto handleConflict;
				}
			}
		}

		assert(false);
	}
}

void invokeSolver(Sat sat, int numConflicts)
{
	swSolver.start();
	scope(exit)
		swSolver.stop();

	sat.cleanup();

	if(sat.varCount == 0)
		return;

	auto solver = new Solver(sat);
	solver.solveSome(numConflicts);
	int nProps = sat.propagate(); // propagate learnt unit clauses

	writefln("c solver removed %s vars", nProps);
	//writefln("c flp stats: %s probes, %s fails (%#.2f %%)", solver.nProbes, solver.nFails, 100*solver.nFails/cast(float)solver.nProbes);
}
