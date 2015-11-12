module sat.main;

import std.stdio;
import std.getopt;
import std.datetime : Clock;
import jive.array;

import sat.sat, sat.parser, sat.solver;
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

	writefln("cnf file: %s", args[1]);

	Sat sat;
	try
	{
		sat = readDimacs(args[1]);
		writefln("read in %.2f s", Clock.currAppTick.msecs/1000.0f);

		sat.writeStatsHeader();

		while(true)
		{
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
