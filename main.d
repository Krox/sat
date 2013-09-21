module main;

import std.stdio;
import sat;

void main(string[] args)
{
	if(args.length != 2)
	{
		writefln("usage: sat <filename>");
		return;
	}

	auto sat = new Sat(args[1]);
	sat.solve();
}
