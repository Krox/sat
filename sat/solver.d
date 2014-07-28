module sat.solver;

import std.stdio;
import std.datetime : Clock;
import jive.array;
import jive.lazyarray;
import sat.sat, sat.clause;



final class Solver
{
	ClauseDB db;
	Sat sat;
	LazyBitArray blocked;
	Lit probe = Lit(0, false);

	long nProbes;
	long nFails;

	this(Sat sat)
	{
		this.sat = sat;
		blocked.resize(sat.varCount*2);

		db = new ClauseDB(sat.varCount);
		foreach(ci, ref c; sat.clauses)
			if(c.length)
				db.addClause(c[]);
	}

	bool failedLiteralProbing(ref Lit branch)
	{
		int bestScore = -1;
		branch = Lit.nil;

		db.bumpLevel();
		blocked.reset();

		auto stop = probe;

		do // TODO: do in in non-arbitrary order to better exploit dominating literals
		{
			if(!db.assign[probe] && !db.assign[probe.neg] && !blocked[probe])
			{
				++nProbes;
				auto r = db.propagate(probe, Reason.descision);

				if(r is null) // there was a conflict
				{
					++nFails;
					return false;
				}

				foreach(x; r[1..$])
					blocked[x] = true;

				int score = cast(int)r.length;
				db.unrollCurrLevel();

				if(score > bestScore)
				{
					bestScore = score;
					branch = probe;
				}
			}
			probe.toInt = (probe.toInt+1)%(db.varCount*2);
		}
		while(probe != stop);

		return true;
	}

	/** throws on UNSAT */
	void solveSome(int numConflicts)
	{
		writefln("c start solver: v=%s c=%s", db.varCount, db.clauseCount);

		while(true)
		{
			Lit branch;
			if(!failedLiteralProbing(branch))
			{
				handleConflict:

				if(numConflicts-- == 0)
					return;

				auto conflictClause = db.analyzeConflict();
				sat.addClause(Array!Lit(conflictClause));

				if(db.currLevel == 0) // conflict on level 0 -> UNSAT
					throw new Unsat;

				//writefln("conflict: %s", conflictClause[]);

				if(conflictClause.length == 1)
				{
					//writefln("found unit: %s", conflictClause[0]);
					db.unrollLevel(0);
					if(db.propagate(conflictClause[0], Reason.unit) is null)
						throw new Unsat;
				}
				else
				{
					//writefln("non-unit conflict                  =======");
					db.unrollLevel(db.level[conflictClause[1].var]);
					auto reason = db.addClause(conflictClause);
					if(db.propagate(conflictClause[0], reason) is null)
						goto handleConflict;
				}
			}
			else if(branch != Lit.nil)
			{
				if(db.propagate(branch, Reason.descision) is null)
					throw new Exception("cannot happen"); // this would have been detected in failed literal probing
			}
			else
			{
				for(int v = 0; v < db.varCount; ++v)
				{
					if(db.assign[Lit(v, false)])
						sat.setLiteral(Lit(v, false));
					else if(db.assign[Lit(v, true)])
						sat.setLiteral(Lit(v, true));
					else assert(false);
				}

				return;
			}
		}

		assert(false);
	}
}

void invokeSolver(Sat sat, int numConflicts)
{
	sat.cleanup();

	if(sat.varCount == 0)
		return;

	auto solver = new Solver(sat);
	solver.solveSome(numConflicts);
	writefln("c stats: %s probes, %s fails (%s %%)", solver.nProbes, solver.nFails, 100*solver.nFails/cast(float)solver.nProbes);
}
