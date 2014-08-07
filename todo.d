#!/usr/bin/rdmd --shebang -O

import std.process;
import std.stdio;
import std.algorithm : splitter, sort;
import std.string : strip, format;
import std.array : join;
import std.getopt;
import std.datetime : StopWatch;
import std.conv : to;
static import std.file;

int main(string[] args)
{
	string solver = "bin/sat";
	string cnfFolder = "./sat-2002-beta/submitted";
	int timeout = 1;
	bool nocheck = false;
	string timingFilename;

	getopt(args,
		"timeout|t", &timeout,
		"nocheck|nc", &nocheck,
		"output|o", &timingFilename,
		"solver|s", &solver);

	if(args.length == 2)
		cnfFolder = args[1];
	else if(args.length != 1)
	{
		writefln("usage: todo.d [options] [folder]");
		return -2;
	}


	auto files = executeShell("find "~cnfFolder~" -type f").output;

	string[] timing;
	int nSat, nUnsat, nTimeout;

	foreach(file; splitter(files, "\n"))
	{
		file = strip(file);
		if(file.length == 0)
			continue;

		writefln("%s", file);
		StopWatch sw;
		sw.start;
		auto r = executeShell("timeout "~to!string(timeout)~"s /usr/bin/time -f \"%U\" -o timeTmp "~solver~" "~file);
		sw.stop;

		switch(r.status)
		{
			case 10:
				writefln("\tsolution found");
				++nSat;
				break;

			case 20:
				writefln("\tUNSAT");
				++nUnsat;
				if(nocheck == false && executeShell("./cryptominisat "~file).status != 20)
				{
					writefln("CHECK FAILED");
					return -1;
				}
				break;

			case 30:
			case 124:
				writefln("\ttimeout");
				++nTimeout;
				continue;

			default:
				writefln("===== ERROR =====");
				writef("%s", r.output);
				return -1;
		}

		timing ~= format("%s %s", sw.peek.msecs/1000.0, file);
	}

	sort(timing);
	if(timingFilename is null)
		timingFilename = executeShell("date +%F_%R.timing").output.strip;
	std.file.write(timingFilename, join(timing, "\n")~"\n");

	writefln("");
	writefln("writing timing to: %s", timingFilename);
	writefln("%s solutions found / %s unsatisfiable / %s timeout", nSat, nUnsat, nTimeout);
	return 0;
}
