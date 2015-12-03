#!/usr/bin/rdmd --shebang --compiler=ldc2 -O -I../jive
module check;

import std.stdio;
import std.getopt;

import sat.sat, sat.parser;

/**
 * returns != 0 if solution is wrong
 */
int main(string[] args)
{
	if(args.length != 3)
	{
		writefln("usage: check <cnf file> <solution file>");
		return -1;
	}

	writefln("c cnf file: %s", args[1]);

	auto sat = readDimacs(args[1]);
	writefln("c read in %.2f s", Clock.currAppTick.msecs/1000.0f);

	auto sol = readSolution(args[2], sat.varCount);
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
