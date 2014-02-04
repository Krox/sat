module sat.main;

import std.stdio;
import jive.array;
import sat.sat, sat.parser, sat.solver, sat.xor, sat.twosat;

void main(string[] args)
{
	if(args.length != 2)
	{
		writefln("usage: sat <filename>");
		return;
	}

	try
	{
		int varCount;
		Array!(Array!Lit) clauses;

		writefln("c reading file %s", args[1]);
		readDimacs(args[1], varCount, clauses);
		writefln("c v=%s c=%s",varCount, clauses.length);

		auto sat = new Sat(varCount, cast(int)clauses.length);
		foreach(ref c; clauses)
			sat.addClause(c);

		writefln("c removed %s variables by unit propagation", sat.propagate());

		solve2sat(sat);
		writefln("c removed %s variables by solving 2-sat", sat.propagate());

		solveXor(sat);
		writefln("c removed %s variables by solving larger xors", sat.propagate());

		sat.solve();
		writefln("s SATISFIABLE");
		sat.writeAssignment();

		foreach(ref c; clauses)
			if(!sat.isSatisfied(c[]))
				throw new Exception("FINAL TEST FAIL");
	}
	catch(Unsat e)
	{
		writefln("s UNSATISFIABLE");
	}
}
