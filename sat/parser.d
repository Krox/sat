module sat.parser;

import jive.array;
import std.file : read;
import std.string : stripLeft;
import std.algorithm : find, max;
import std.math : abs;
import std.stdio;
import sat.sat;

struct Pair { Lit a,b; }
struct Triple { Lit a,b,c; }

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

/**
 * read a .cnf file in dimacs format.
 * NOTE: 'p' lines are not required
 */
void readDimacs(string filename, ref int varCount, ref Array!Lit unary, ref Array!Pair binary, ref Array!Triple ternary, ref Array!(Array!Lit) clauses)
{
	// read the file (without UTF validation to save time)
	auto buf = cast(string)read(filename);

	Array!Lit cl;
	varCount = 0;

	while(true)
	{
		buf = stripLeft(buf);

		if(buf.length == 0)
			break;

		switch(buf[0])
		{
			case 'c':
				buf = find(buf, "\n")[1..$];
				break;

			case 'p':
				buf = buf[1..$];
				buf = stripLeft(buf);
				if(buf[0..3] != "cnf")
					throw new Exception("dimacs file with invalid 'p' line");
				buf = stripLeft(buf[3..$]);
				int dimacsVarCount = parseInt(buf);
				buf = stripLeft(buf);
				int dimacsClauseCount = parseInt(buf);
				varCount = max(varCount, dimacsVarCount);
				writefln("header says %s vars and %s clauses", dimacsVarCount, dimacsClauseCount);
				break;

			default:

				while(true)
				{
					int x = parseInt(buf);
					if(x == 0)
						break;
					varCount = max(varCount, abs(x));
					cl.pushBack(Lit.fromDimacs(x));
					buf = stripLeft(buf);
				}

				switch(cl.length)
				{
					case 0:
						throw new Unsat;
					case 1:
						unary.pushBack(cl[0]);
						break;
					case 2:
						binary.pushBack(Pair(cl[0], cl[1]));
						break;
					case 3:
						ternary.pushBack(Triple(cl[0], cl[1], cl[2]));
						break;
					default:
						clauses.pushBack(cl);
						break;
				}

				cl.resize(0);
				break;
		}
	}
}
