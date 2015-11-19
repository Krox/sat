module sat.main;

import std.stdio;
import std.getopt;
import std.datetime : Clock;

import sat.sat, sat.parser, sat.solver;

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
	string solutionFilename, outputFilename;
	getopt(args, "skipsolution|s", &skipSolution,
	             "solution", &solutionFilename,
				 "output|o", &outputFilename);

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

		solve(sat);
		writefln("c solution found");

		// time statistics
		writeStats();

		// solution
		if(outputFilename !is null)
			sat.assign.print(File(outputFilename, "w"));
		else if(!skipSolution)
			sat.assign.print(stdout);

		return 10;
	}
	catch(Unsat e)
	{
		// time statistics
		writeStats();
		writefln("s UNSATISFIABLE");
		return 20;
	}

	return -2;
}
