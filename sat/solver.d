module sat.solver;

import std.stdio;
import std.datetime : Clock;
import jive.array;
import sat.sat, sat.clause;

final class Solver
{
	ClauseDB db;

	this(ClauseDB db)
	{
		this.db = db;
	}

	bool forceFailedLiteral(ref Lit suggestedLiteral) // false, if a conflict was discovered (resulting assign is NOT clean)
	{
		int bestScore = -1;
		suggestedLiteral = Lit.nil;
		Lit stop;
		Lit x;

		do // TODO: use some non-arbitrary order here (in particular, exploit dominating literals)
		{
			if(!db.assign[x] && !db.assign[x.neg])
			{
				if(auto posScore = cast(int)db.propagate(x).length)
				{
					db.unroll(x);

					if(auto negScore = cast(int)db.propagate(x.neg).length)	// both work -> unroll (and score it for decision)
					{
						db.unroll(x.neg);

						int score = posScore + negScore + posScore*negScore;	// this scoring can/should be tweaked
						if(score > bestScore)
						{
							suggestedLiteral = x;
							bestScore = score;
						}
					}
					else	// positive worked, negative not
					{
						db.propagate(x);

						bestScore = -1;
						suggestedLiteral = Lit.nil;
						stop = x;
					}
				}
				else
				{
					if(db.propagate(x.neg))	// negative worked, positive not
					{
						bestScore = -1;
						suggestedLiteral = Lit.nil;
						stop = x;
					}
					else	// both dont work -> conflict
						return false;
				}
			}

			x.toInt = (x.toInt+2) % (2*db.varCount);
		}
		while(x != stop);

		return true;
	}

	/** return null on UNSAT */
	bool[] solve(int timeout)
	{
		writefln("c start solver: v=%s c=%s", db.varCount, db.clauseCount);
		Array!Lit decStack;
		decStack.reserve(db.varCount);	// wont grow that large if we did anything right

		while(true)
		{
			Lit x;
			if(forceFailedLiteral(x) == false)	// if forcing fails -> conflict
			{
				if(decStack.empty)	// no decision to revert -> UNSAT
					return null;
				if(timeout && Clock.currAppTick.seconds >= timeout)
					throw new Timeout();
				Lit y = decStack.popBack;
				db.unroll(y);
				if(db.propagate(y.neg).length == 0)
					throw new Exception("nah, cant happen");
				continue;
			}

			if(x == Lit.nil)	// no free literal -> solution found
				return db.assign[];

			decStack.pushBack(x);
			if(db.propagate(x).length == 0)
				throw new Exception("cannot happen");	// this would have been detected in failed literal probing
		}
	}
}
