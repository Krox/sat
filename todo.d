#!/usr/bin/rdmd --shebang -O

import std.process;
import std.stdio;
import std.algorithm : splitter, sort, map;
import std.string : strip, format;
import std.array : join;
import std.getopt;
import std.datetime : StopWatch;
import std.conv : to;
import std.range;
import std.file : readText, isDir, write;

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

	string[] filenames;
	bool readDir = isDir(cnfFolder);
	if(readDir)
		filenames = array(splitter(executeShell("find "~cnfFolder~" -type f").output, "\n"));
	else
		filenames = cnfFolder.readText.splitter("\n").map!"a.find(\" \")".array;

	string[] timing;
	int nSat, nUnsat, nTimeout;

	foreach(i, file; filenames)
	{
		file = strip(file);
		if(file.length == 0)
			continue;

		writefln("[%s / %s] %s", i, filenames.length, file);
		StopWatch sw;
		sw.start;
		auto r = executeShell("timeout "~to!string(timeout)~"s /usr/bin/time -f \"%U\" -o timeTmp "~solver~" -osolutionTmp "~file);
		sw.stop;

		switch(r.status)
		{
			case 10:
				writef("\tsolution found... ");
				auto s = executeShell("bin/sat --solution=solutionTmp "~file);
				if(s.status == 0)
					writefln("checked");
				else
				{
					writefln("CHECK FAILED");
					return -1;
				}
				++nSat;
				break;

			case 20:
				writef("\tunsat... ");
				++nUnsat;
				if(nocheck)
					writefln("check skipped");
				else if(executeShell("./cryptominisat "~file).status == 20)
					writefln("checked");
				else
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

	if(readDir)
		sort(timing);
	if(timingFilename is null)
		timingFilename = executeShell("date +%F_%R.timing").output.strip;
	write(timingFilename, join(timing, "\n")~"\n");

	writefln("");
	writefln("writing timing to: %s", timingFilename);
	writefln("%s solutions found / %s unsatisfiable / %s timeout", nSat, nUnsat, nTimeout);
	return 0;
}
