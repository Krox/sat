module sat.main;

import std.stdio;
import std.getopt;
import std.datetime : Clock;
import jive.array;

import sat.sat, sat.parser, sat.solver, sat.xor, sat.twosat, sat.simplify;
import sat.varelim;
import sat.stats;

/**
 * returns:
 *     10 if solution was found
 *     20 if unsatisfiable
 *     30 on timeout
 *     negative on errors
 */
int main(string[] args)
{
	bool skipSolution = false;
	getopt(args, "skipsolution|s", &skipSolution);

	if(args.length != 2)
	{
		writefln("usage: sat <filename>");
		return -1;
	}

	int varCount;
	Array!(Array!Lit) clauses;

	writefln("cnf file: %s", args[1]);
	readDimacs(args[1], varCount, clauses);
	writefln("vars: %s, clauses: %s",varCount, clauses.length);


	auto sat = new Sat(varCount, cast(int)clauses.length);

	try
	{
		foreach(ref c; clauses)
			sat.addClause(c, true);
		sat.propagate(); // propagate units clauses in cnf

		sat.writeStatsHeader();

		while(!sat.assign.complete)
		{
			solve2sat(sat);

			simplify(sat);

			solve2sat(sat);

			solveXor(sat);

			varElim(sat);

			sat.cleanup();

			new Solver(sat).run(1000);
			int nProps = sat.propagate(); // propagate learnt unit clauses

			sat.writeStatsLine();
		}

		sat.writeStatsFooter();

		writeStats();

		writefln("s SATISFIABLE");

		sat.assign.extend();

		if(!skipSolution)
			sat.assign.writeAssignment();

		foreach(ref c; clauses)
			if(!sat.assign.isSatisfied(c[]))
				throw new Exception("FINAL TEST FAIL");

		return 10;
	}
	catch(Unsat e)
	{
		sat.writeStatsFooter();
		writeStats();
		writefln("s UNSATISFIABLE");
		return 20;
	}
	catch(Timeout e)
	{
		writeStats();
		writefln("c TIMEOUT");
		return 30;
	}
}
