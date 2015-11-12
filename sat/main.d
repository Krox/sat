module sat.main;

import std.stdio;
import std.getopt;
import std.datetime : Clock;
import jive.array;

import sat.sat, sat.parser, sat.solver, sat.twosat;
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
	string solutionFilename;
	getopt(args, "skipsolution|s", &skipSolution,
	             "solution", &solutionFilename);

	if(args.length != 2)
	{
		writefln("usage: sat <filename>");
		return -1;
	}

	writefln("c cnf file: %s", args[1]);

	Sat sat;
	try
	{
		sat = readDimacs(args[1]);
		writefln("c read in %.2f s", Clock.currAppTick.msecs/1000.0f);

		if(solutionFilename !is null)
		{
			auto sol = readSolution(solutionFilename, sat.varCount);
			if(sat.checkSolution(sol))
			{
				writefln("c solution checked");
				return 0;
			}
			else
			{
				writefln("INVALID SOLUTION");
				return -1;
			}
		}

		sat.writeStatsHeader();

		while(true)
		{
			new TwoSat(sat).run();

			sat.writeStatsLine();
			bool solved = new Solver(sat).run(1000);

			if(solved || sat.units.length >= 100)
				sat.cleanup;

			if(solved)
			{
				assert(sat.varCount == 0);
				break;
			}
		}

		sat.writeStatsFooter();

		writeStats();

		writefln("s SATISFIABLE");

		sat.assign.extend();
		if(!skipSolution)
			sat.assign.print();

		return 10;
	}
	catch(Unsat e)
	{
		sat.writeStatsFooter();
		writeStats();
		writefln("s UNSATISFIABLE");
		return 20;
	}

	return -2;
}
