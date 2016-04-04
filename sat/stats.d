module sat.stats;

/**
 * global variables for configuration and statistics;
 */

private import std.stdio;
public import std.datetime : Clock, StopWatch;
private import math.histogram;

StopWatch swTarjan, swSubsume, swSubsumeBinary, swXor, swSolver, swVarElim, swCleanup, swSolverStartup;

long nConflicts;
long nLitsOtfRemoved;
long nLitsLearnt;

Histogram watchHisto;

struct config
{
	static:
	bool binarySubsume = false;
	bool watchStats = false;
	int otf = 2;
}

void initStats()
{
	if(config.watchStats)
		watchHisto = Histogram(-0.5, 20.5, 21);
}

void writeStats()
{
	auto total = Clock.currAppTick;
	writefln("c =============================== stats ===============================");

	if(config.watchStats)
	{
		writefln("watch-list size:");
		watchHisto.write;
	}

	writefln("c conflicts: %s", nConflicts);
	if(config.otf > 0)
		writefln("c otf removed %4.1f %% of literals", 100f*nLitsOtfRemoved/nLitsLearnt);

	writefln("c tarjan     %#6.2f s (%#4.1f %%)", swTarjan.peek.msecs/1000.0f, 100f*swTarjan.peek.msecs/total.msecs);
	writefln("c xor        %#6.2f s (%#4.1f %%)", swXor.peek.msecs/1000.0f, 100f*swXor.peek.msecs/total.msecs);
	writefln("c subsume    %#6.2f s (%#4.1f %%)", swSubsume.peek.msecs/1000.0f, 100f*swSubsume.peek.msecs/total.msecs);
	writefln("c subsumeBin %#6.2f s (%#4.1f %%)", swSubsumeBinary.peek.msecs/1000.0f, 100f*swSubsumeBinary.peek.msecs/total.msecs);
	writefln("c varElim    %#6.2f s (%#4.1f %%)", swVarElim.peek.msecs/1000.0f, 100f*swVarElim.peek.msecs/total.msecs);
	writefln("c cleanup    %#6.2f s (%#4.1f %%)", swCleanup.peek.msecs/1000.0f, 100f*swCleanup.peek.msecs/total.msecs);
	writefln("c solverInit %#6.2f s (%#4.1f %%)", swSolverStartup.peek.msecs/1000.0f, 100f*swSolverStartup.peek.msecs/total.msecs);
	writefln("c solver     %#6.2f s (%#4.1f %%)", swSolver.peek.msecs/1000.0f, 100f*swSolver.peek.msecs/total.msecs);
	writefln("c total      %#6.2f s", total.msecs/1000.0f);
}
