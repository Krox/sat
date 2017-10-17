module sat.main;

import std.stdio;
import std.getopt : getopt, defaultGetoptPrinter;
import core.time;
import core.stdc.signal;

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
		"probing", "Failed literal probing. (0=none, 1=preprocessing, 2=inprocessing)", &config.probing,
		"binary-subsume", "Binary self-subsuming resolution on top-level.", &config.binarySubsume,
		"xor", "Gaussian elimination of xor clauses on top-level.", &config.xor,
		"otf", "Simplification of learnt clauses. (0=none, 1=basic, 2=full)", &config.otf,
		"lhbr", "Lazy hyper-binary resolution.", &config.lhbr,
		"watch-stats", "Keep and print statistics on watch-lists lengths.", &config.watchStats,
		"c", "don't solve, just check solution", &doCheck,
		);

	// if -h was passed, print help text and quit
	if(helpInfo.helpWanted || (args.length != 2 && args.length != 3) || (doCheck && args.length != 3))
	{
		defaultGetoptPrinter("usage: sat <cnf input> [solution output]\n       sat -c <cnf input> <solution input>", helpInfo.options);
		return 0;
	}

	signal(SIGINT, &interruptHandler);

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

	if(sol !is null) // found a solution
	{
		writefln("s SATISFIABLE");
		if(args.length >= 3)
			sol.print(File(args[2], "w"));
		writeStats();
		return 10;
	}
	else if(!interrupted) // unsatisfiable
	{
		writefln("s UNSATISFIABLE");
		if(args.length >= 3)
			File(args[2], "w").writefln("s UNSATISFIABLE");
		writeStats();
		return 20;
	}
	else // interrupted
	{
		writefln("c INTERRUPTED");
		writeStats();
		return 30;
	}
}
