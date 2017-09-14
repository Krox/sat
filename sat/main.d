module sat.main;

import std.stdio;
import std.getopt : getopt, defaultGetoptPrinter;
import core.time;

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
	bool doCheck = false;

	auto helpInfo = getopt(args,
		"binary-subsume", "Binary self-subsuming resolution on top-level.", &config.binarySubsume,
		"xor", "Gaussian elimination of xor clauses on top-level.", &config.xor,
		"otf", "Simplification of learnt clauses. (0=none, 1=basic, 2=full)", &config.otf,
		"hyperBinary", "Lazy hyper-binary resolution.", &config.hyperBinary,
		"watch-stats", "Keep and print statistics on watch-lists lengths.", &config.watchStats,
		"c", "don't solve, just check solution", &doCheck,
		);

	// if -h was passed, print help text and quit
	if(helpInfo.helpWanted || (args.length != 2 && args.length != 3) || (doCheck && args.length != 3))
	{
		defaultGetoptPrinter("usage: sat <cnf input> [solution output]\n       sat -c <cnf input> <solution input>", helpInfo.options);
		return 0;
	}

	// if check was requested, do so and quit
	if(doCheck)
	{
		writefln("c reading cnf file: %s", args[1]);
		auto sat = readDimacs(args[1]);

		writefln("c reading solution file: %s", args[2]);
		auto sol = readSolution(args[2], sat.varCount);

		if(sat.checkSolution(sol))
		{
			writefln("c solution checked");
			return 0;
		}
		else
		{
			writefln("c INVALID SOLUTION");
			return -1;
		}
	}

	writefln("c cnf file: %s", args[1]);

	auto sat = readDimacs(args[1]);
	writefln("c read in %.2f s", (MonoTime.currTime - startTime).total!"msecs"*1.0e-3);

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
