module sat.parser;

import std.file : read;
import std.string : stripLeft;
import std.algorithm : find, max;
import std.math : abs;
import std.stdio;

import jive.array;
import jive.bitarray;

import sat.sat;

/** same as std.conv.parse!int but faster (and probably less general) */
private int parseInt(ref string buf)
{
	bool neg = buf[0] == '-';
	if(neg)
		buf = buf[1..$];
	assert('0' <= buf[0] && buf[0] <= '9');
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
		if(buf[0] == 'c')
			buf = find(buf, "\n")[1..$];
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
		throw new Exception("dimacs file with invalid 'p' line");
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

	return sat;
}

BitArray readSolution(string filename, int varCount)
{
	// read the file (without UTF validation to save time)
	auto buf = cast(string)read(filename);

	buf = skipComments(buf);
	if(buf[0..13] != "s SATISFIABLE")
		throw new Exception("solution with invalid 's' line");
	buf = buf[13..$];
	buf = skipComments(buf);

	auto sol = BitArray(varCount*2);

	if(buf[0] != 'v')
		throw new Exception("no 'v' line in solution");
	buf = buf[1..$];

	for(int i = 0; i < varCount; ++i)
	{
		buf = stripLeft(buf);
		auto x = Lit.fromDimacs(parseInt(buf));
		assert(x.var == i);
		sol[x] = true;
	}

	return sol;
}
