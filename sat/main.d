module sat.main;

import std.stdio;
import std.getopt : getopt, defaultGetoptPrinter;
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
	auto helpInfo = getopt(args,
		"binary-subsume", "Binary self-subsuming resolution on top-level.", &config.binarySubsume,
		"xor", "Gaussian elimination of xor clauses on top-level.", &config.xor,
		"otf", "Simplification of learnt clauses. (0=none, 1=basic, 2=full)", &config.otf,
		"hyperBinary", "Lazy hyper-binary resolution.", &config.hyperBinary,
		"watch-stats", "Keep and print statistics on watch-lists lengths.", &config.watchStats,
		);

	// if -h was passed, print help text and quit
	if(helpInfo.helpWanted || (args.length != 2 && args.length != 3))
	{
		defaultGetoptPrinter("usage: sat <cnf input> [solution output]", helpInfo.options);
		return 0;
	}

	writefln("c cnf file: %s", args[1]);

	auto sat = readDimacs(args[1]);
	writefln("c read in %.2f s", Clock.currAppTick.msecs/1000.0f);

	auto sol = solve(sat);

	if(sol !is null)
	{
		// verdict
		writefln("s SATISFIABLE");

		// print solution to file
		if(args.length >= 3)
			sol.print(File(args[2], "w"));

		// time statistics
		writeStats();

		return 10;
	}
	else
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
}
