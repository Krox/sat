module sat.parser;

import jive.array;
import std.file : readText;
import std.string : stripLeft;
import std.algorithm : find, max;
import std.conv : parse;
import std.math : abs;
import sat.sat;

/**
 * read a .cnf file in dimacs format.
 * NOTE: 'p' lines are not required
 */
void readDimacs(string filename, ref int varCount, ref Array!Clause clauses)
{
	auto buf = readText(filename);
	Array!Lit clauseBuf;
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
				int dimacsVarCount = parse!int(buf);
				buf = stripLeft(buf);
				int dimacsClauseCount = parse!int(buf);

				varCount = max(varCount, dimacsVarCount);
				clauses.reserve(dimacsClauseCount);
				break;

			default:
				while(true)
				{
					int x = parse!int(buf);
					if(x == 0)
						break;
					varCount = max(varCount, abs(x));
					clauseBuf.pushBack(Lit.fromDimacs(x));
					buf = stripLeft(buf);
				}
				clauses.pushBack(Clause(clauseBuf[]));
				clauseBuf.resize(0);
				break;
		}
	}
}
