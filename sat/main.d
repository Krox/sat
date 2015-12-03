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
	if(args.length != 2 && args.length != 3)
	{
		writefln("usage: sat <cnf input> [solution output]");
		return -1;
	}

	writefln("c cnf file: %s", args[1]);

	Sat sat;
	try
	{
		sat = readDimacs(args[1]);
		writefln("c read in %.2f s", Clock.currAppTick.msecs/1000.0f);

		solve(sat);

		// verdict
		writefln("s SATISFIABLE");

		// print solution to file
		if(args.length >= 3)
			sat.assign.print(File(args[2], "w"));

		// time statistics
		writeStats();

		return 10;
	}
	catch(Unsat e)
	{
		// verdict
		writefln("s UNSATISFIABLE");

		// print verdict to file
		if(args.length >= 3)
			File(args[2], "w").writefln("UNSAT");

		// time statistics
		writeStats();

		return 20;
	}

	return -2;
}
