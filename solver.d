module solver;

import std.stdio;
import jive.array;
import clause;

final class Solver
{
	ClauseDB db;

	this(ClauseDB db)
	{
		this.db = db;
	}

	bool forceFailedLiteral(ref int suggestedLiteral) // false, if a conflict was discovered (resulting assign is NOT clean)
	{
		int bestScore = -1;
		suggestedLiteral = -1;
		int stop = 0;
		int x = 0;

		do // TODO: use some non-arbitrary order here (in particular, exploit dominating literals)
		{
			if(!db.assign[x] && !db.assign[x^1])
			{
				if(auto posScore = cast(int)db.propagate(x).length)
				{
					db.unroll(x);

					if(auto negScore = cast(int)db.propagate(x^1).length)	// both work -> unroll (and score it for decision)
					{
						db.unroll(x^1);

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
						suggestedLiteral = -1;
						stop = x;
					}
				}
				else
				{
					if(db.propagate(x^1))	// negative worked, positive not
					{
						bestScore = -1;
						suggestedLiteral = -1;
						stop = x;
					}
					else	// both dont work -> conflict
						return false;
				}
			}

			x = (x+2)%(db.varCount*2);
		}
		while(x != stop);

		return true;
	}

	/** return null on UNSAT */
	bool[] solve()
	{
		writefln("c start solver: v=%s c=%s", db.varCount, db.clauseCount);
		Array!int decStack;
		decStack.reserve(db.varCount);	// wont grow that large if we did anything right

		while(true)
		{
			int x = -1;
			if(forceFailedLiteral(x) == false)	// if forcing fails -> conflict
			{
				if(decStack.empty)	// no decision to revert -> UNSAT
					return null;
				int y = decStack.popBack;
				db.unroll(y);
				if(db.propagate(y^1).length == 0)
					throw new Exception("nah, cant happen");
				continue;
			}

			if(x == -1)	// no free literal -> solution found
				return db.assign[];

			decStack.pushBack(x);
			if(db.propagate(x).length == 0)
				throw new Exception("cannot happen");	// this would have been detected in failed literal probing
		}
	}
}
