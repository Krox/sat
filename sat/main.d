module sat.main;

import std.stdio;
import std.getopt;
import std.datetime : Clock;
import jive.array;

import sat.sat, sat.parser, sat.searcher, sat.twosat;

private import core.bitop: bsr, popcnt;

int luby(int i)
{
	if(popcnt(i+1) == 1)
		return (i+1)/2;
	else
		return luby(i-(1<<bsr(i))+1);
}

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

		sat.writeStatsHeader();

		Searcher searcher = null;
		for(int i = 1; ; ++i)
		{
			// 2-sat is cheap, solver restart is expensive, so run it whenever the solver is down anyway
			if(searcher is null)
				new TwoSat(sat).run();

			// run the CDCL searcher
			if(searcher is null)
				searcher = new Searcher(sat);
			sat.writeStatsLine();
			bool solved = searcher.run(luby(i)*100);

			if(solved)
			{
				delete searcher;
				sat.cleanup;
				assert(sat.varCount == 0);
				break;
			}

			if(sat.units.length >= 100)
			{
				delete searcher;
				sat.cleanup;
			}
		}

		sat.writeStatsFooter();
		writefln("c solution found");
		writeStats();

		sat.assign.extend();
		if(outputFilename !is null)
			sat.assign.print(File(outputFilename, "w"));
		else if(!skipSolution)
			sat.assign.print(stdout);

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
