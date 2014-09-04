module sat.main;

import std.stdio;
import std.getopt;
import jive.array;
import sat.sat, sat.parser, sat.solver, sat.xor, sat.twosat;
import std.datetime : Clock;

/**
 * returns:
 *     10 if solution was found
 *     20 if unsatisfiable
 *     30 on timeout
 *     negative on errors
 */
int main(string[] args)
{
	int timeout = 0;
	getopt(args, "timeout|t", &timeout);

	if(args.length != 2)
	{
		writefln("usage: sat <filename>");
		return -1;
	}

	try
	{
		int varCount;
		Array!(Array!Lit) clauses;

		writefln("c reading file %s", args[1]);
		readDimacs(args[1], varCount, clauses);
		writefln("c v=%s c=%s",varCount, clauses.length);

		auto sat = new Sat(varCount, cast(int)clauses.length);
		foreach(ref c; clauses)
			sat.addClause(c, true);

		writefln("c removed %s variables by unit propagation", sat.propagate());

		for(int round = 1; !sat.assign.complete; ++round)
		{
			auto roundStart = Clock.currAppTick;

			writefln("c ============================== round %s ==============================", round);

			solve2sat(sat);

			solveXor(sat);

			auto solverStart = Clock.currAppTick;

			invokeSolver(sat, 1000); // TODO: tweak this number (actually, do something more sophisticated than a number)

			auto roundEnd = Clock.currAppTick;

			writefln("c used %#.1f s for inprocessing, %#.1f s for solving (total is %#.1f s)",
				(solverStart-roundStart).msecs/1000.0, (roundEnd-solverStart).msecs/1000.0, roundEnd.msecs/1000.0);
		}

		writefln("s SATISFIABLE");

		sat.assign.extend();
		sat.assign.writeAssignment();

		foreach(ref c; clauses)
			if(!sat.assign.isSatisfiedOuter(c[]))
				throw new Exception("FINAL TEST FAIL");

		return 10;
	}
	catch(Unsat e)
	{
		writefln("s UNSATISFIABLE");
		return 20;
	}
	catch(Timeout e)
	{
		writefln("c TIMEOUT");
		return 30;
	}
}
