module solver;

import std.stdio;
import jive.array;
import clause;

final class Solver
{
	ClauseDB db;

	this(ClauseDB db)
	{
		this.db = db; // note: clauses inside db are not set yet. So dont try to do anything here
	}

	bool forceFailedLiteral(ref int suggestedLiteral) // false, if a conflict was discovered (resulting assign is NOT clean)
	{
		start:
		int bestScore = -1;
		suggestedLiteral = -1;
		bool success = false;

		for(int x = 0; x < 2*db.varCount; x+=2)	// TODO: use some non-arbitrary order here (in particular, exploit dominating literals)
			if(!db.assign[x] && !db.assign[x^1])
			{
				if(int posScore = db.propagate(x))
				{
					db.unroll(x);

					if(int negScore = db.propagate(x^1))	// both work -> unroll (and score it for decision)
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
						success = true;
					}
				}
				else
				{
					if(db.propagate(x^1))	// negative worked, positive not
						success = true;
					else	// both dont work -> conflict
						return false;
				}
			}

		if(success)
			goto start;

		return true;
	}

	bool[] solve()
	{
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
				if(0 == db.propagate(y^1))
					throw new Exception("nah, cant happen");
				continue;
			}

			if(x == -1)	// no free literal -> solution found
			{
				writefln("solution found");
				return db.assign[];
			}

			decStack.pushBack(x);
			if(0 == db.propagate(x))
				throw new Exception("cannot happen");	// this would have been detected in failed literal probing
		}
	}
}
