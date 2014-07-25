module sat.solver;

import std.stdio;
import std.datetime : Clock;
import jive.array;
import jive.lazyarray;
import sat.sat, sat.clause;

final class Solver
{
	ClauseDB db;
	LazyBitArray blocked;

	this(ClauseDB db)
	{
		this.db = db;
		blocked.resize(db.varCount*2);
	}

	bool failedLiteralProbing(ref Lit branch)
	{
		int bestScore = -1;
		branch = Lit.nil;

		db.bumpLevel();
		blocked.reset();

		for(Lit lit = Lit(0, false); lit.toInt < db.varCount*2; ++lit.toInt) // TODO: do in in non-arbitrary order to better exploit dominating literals
			if(!db.assign[lit] && !db.assign[lit.neg] && !blocked[lit])
			{
				auto r = db.propagate(lit, Reason.descision);

				if(r is null) // there was a conflict
					return false;

				foreach(x; r[1..$])
					blocked[x] = true;

				int score = cast(int)r.length;
				db.unrollCurrLevel();

				if(score > bestScore)
				{
					bestScore = score;
					branch = lit;
				}
			}

		return true;
	}

	/** return null on UNSAT */
	bool[] solve(int timeout = 0)
	{
		writefln("c start solver: v=%s c=%s", db.varCount, db.clauseCount);

		while(true)
		{
			Lit branch;
			if(!failedLiteralProbing(branch))
			{
				handleConflict:

				auto conflictClause = db.analyzeConflict();

				if(db.currLevel == 0) // conflict on level 0 -> UNSAT
					return null;

				if(conflictClause.length == 1)
				{
					db.unrollLevel(0);
					if(db.propagate(conflictClause[0], Reason.unit) is null)
						return null;
				}
				else
				{
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
				return db.assign[];
		}

		assert(false);
	}
}
