module sat.parser;

import std.file : read;
import std.string : stripLeft;
import std.format;
import std.algorithm : find, max;
import std.math : abs;
import std.stdio;

import jive.array;
import jive.bitarray;

import sat.sat;

/** same as std.conv.parse!int but faster (and probably less general) */
private int parseInt(ref string buf)
{
	bool neg = buf.length && buf[0] == '-';
	if(neg)
		buf = buf[1..$];
	if(buf.length == 0)
		throw new Exception("dimacs parser: unexpected end of file");
	if(!('0' <= buf[0] && buf[0] <= '9'))
		throw new Exception(format("dimacs parser: found '%s' when expecting a number", buf[0]));
	int r = 0;
	while(buf.length && '0' <= buf[0] && buf[0] <= '9')
	{
		r = r*10+buf[0]-'0';
		buf = buf[1..$];
	}

	if(neg)
		return -r;
	else
		return r;
}

// skip comments and whitespace
private string skipComments(string buf)
{
	while(true)
	{
		buf = stripLeft(buf); // strip whitespace
		if(buf.length && buf[0] == 'c')
			buf = find(buf, "\n");
		else
			break;
	}
	return buf;
}

/**
 * read a .cnf file in dimacs format.
 */
Sat readDimacs(string filename)
{
	// read the file (without UTF validation to save time)
	auto buf = cast(string)read(filename);

	Array!Lit cl;

	buf = skipComments(buf);
	if(buf[0..5] != "p cnf")
		throw new Exception("dimacs parser: invalid (or missing) 'p' line");
	buf = buf[5..$];
	buf = stripLeft(buf);
	int varCount = parseInt(buf);
	buf = stripLeft(buf);
	int clauseCount = parseInt(buf);
	writefln("c header says %s vars and %s clauses", varCount, clauseCount);

	auto sat = new Sat(varCount);

	for(int i = 0; i < clauseCount; ++i)
	{
		buf = skipComments(buf);

		cl.resize(0);

		while(true)
		{
			int x = parseInt(buf);
			if(x == 0)
				break;
			cl.pushBack(Lit.fromDimacs(x));
			buf = stripLeft(buf);
		}

		sat.addClause(cl[], true);
	}

	buf = skipComments(buf);
	if(buf.length)
		throw new Exception("dimacs parser: unused data at end of file");

	return sat;
}

BitArray readSolution(string filename, int varCount)
{
	// read the file (without UTF validation to save time)
	auto buf = cast(string)read(filename);

	buf = skipComments(buf);
	if(buf[0..5] == "s UNSATISFIABLE")
		assert(false, "TODO");
	if(buf[0..13] == "s SATISFIABLE")
		buf = buf[13..$]; // cryptominisat, lingeling, this solver
	else if(buf[0..3] == "SAT")
		buf = buf[3..$]; // minisat
	else
		throw new Exception(format("dimacs parser: solution with invalid 's' line: %s...", buf[0..13]));
	buf = skipComments(buf);

	auto sol = BitArray(varCount*2);

	while(true)
	{
		buf = stripLeft(buf);
		if(buf.length == 0)
			break;
		if(buf.length && buf[0] == 'v')
		{
			buf = buf[1..$];
			continue;
		}
		auto i = parseInt(buf);
		if(i == 0)
			continue;
		auto x = Lit.fromDimacs(i);
		if(x.var >= varCount)
		{
			writefln("%s %s", x, varCount);
			throw new Exception("dimacs parser: solution contains invalid variable");
		}
		if(sol[x])
			throw new Exception("dimacs parser: solution is redundant");
		if(sol[x.neg])
			throw new Exception("dimacs parser: solution is contradictory");
		sol[x] = true;
	}

	for(int i = 0; i < varCount; ++i)
		if(!sol[Lit(i,false)] && !sol[Lit(i,true)])
			throw new Exception("dimacs parser: solution is incomplete");

	return sol;
}
