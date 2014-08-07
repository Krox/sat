module sat.main;

import std.stdio;
import std.getopt;
import jive.array;
import sat.sat, sat.parser, sat.solver, sat.xor, sat.twosat;

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
			sat.addClause(c);

		writefln("c removed %s variables by unit propagation", sat.propagate());

		for(int round = 1; !sat.assign.complete; ++round)
		{
			writefln("c =========================== round %s ===========================", round);

			solve2sat(sat);
			writefln("c removed %s variables by solving 2-sat", sat.propagate());

			solveXor(sat);
			writefln("c removed %s variables by solving larger xors", sat.propagate());

			invokeSolver(sat, 1000); // TODO: tweak this number (actually, do something more sophisticated than a number)
			writefln("c removed %s variables by invoking solver", sat.propagate());
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
