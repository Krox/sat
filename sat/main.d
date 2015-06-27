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
	Array!Lit unary;
	Array!Pair binary;
	Array!Triple ternary;
	Array!(Array!Lit) clauses;

	writefln("cnf file: %s", args[1]);
	readDimacs(args[1], varCount, unary, binary, ternary, clauses);
	writefln("read %s / %s / %s / %s clauses in %.2f s", unary.length, binary.length, ternary.length, clauses.length, Clock.currAppTick.msecs/1000.0f);

	auto sat = new Sat(varCount, cast(int)clauses.length);

	try
	{
		foreach(c; unary)
			sat.addUnary(c);
		foreach(c; binary)
			sat.addBinary(c.a, c.b);
		foreach(c; ternary)
			sat.addTernary(c.a, c.b, c.c);
		foreach(ref c; clauses)
			sat.addClause(c[], true);
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

		foreach(c; unary)
			if(!sat.assign.isSatisfied(c))
				throw new Exception("FINAL TEST FAIL");
		foreach(c; binary)
			if(!sat.assign.isSatisfied(c.a, c.b))
				throw new Exception("FINAL TEST FAIL");
		foreach(c; ternary)
			if(!sat.assign.isSatisfied(c.a, c.b, c.c))
				throw new Exception("FINAL TEST FAIL");
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

	return -2;
}
