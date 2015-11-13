module sat.main;

import std.stdio;
import std.getopt;
import std.datetime : Clock;
import jive.array;

import sat.sat, sat.parser, sat.solver, sat.twosat;

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

		Solver solver = null;
		for(int i = 1; ; ++i)
		{
			// 2-sat is cheap, solver restart is expensive, so run it whenever the solver is down anyway
			if(solver is null)
				new TwoSat(sat).run();

			// run the solver
			if(solver is null)
				solver = new Solver(sat);
			sat.writeStatsLine();
			bool solved = solver.run(luby(i)*100);

			if(solved)
			{
				delete solver;
				sat.cleanup;
				assert(sat.varCount == 0);
				break;
			}

			if(sat.units.length >= 100)
			{
				delete solver;
				sat.cleanup;
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
