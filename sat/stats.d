module sat.stats;

/**
 * global variables for configuration and statistics;
 */

private import std.stdio;
public import std.datetime : Clock, StopWatch;
private import math.histogram, math.gnuplot;

StopWatch swTarjan, swSubsume, swSubsumeBinary, swXor, swSolver, swVarElim, swCleanup, swSolverStartup;

long nLearnt;
long nLitsOtfRemoved;
long nLitsLearnt;

// length of watchlists traversed
Histogram watchHisto;

// number of propagations/conflicts
long nBinProps;
long nBinConfls;
long nLongProps;
long nLongConfls;
long nConflicts() { return nBinConfls + nLongConfls; }
long nHyperBinary;
long nXorUnits;
long nXorEqus;

struct config
{
	static:
	// features of the solver
	bool binarySubsume = false;
	int otf = 2;
	bool hyperBinary = true;
	bool xor = true;

	// statistic output
	bool watchStats = false;
}

void initStats()
{
	if(config.watchStats)
		watchHisto = Histogram(-0.5, 20.5, 21);
}

void writeStats()
{
	if(config.watchStats)
	{
		auto plot = new Gnuplot;
		plot.plot(watchHisto, "watch-list size");
	}

	writefln("c ========================= propagation stats =========================");
	writefln("c watchlist size: %#10.2f", watchHisto.avg);
	writefln("c binary props:   %#10s", nBinProps);
	writefln("c binary confls:  %#10s", nBinConfls);
	writefln("c long props:     %#10s (%#4.1f %% of watches)", nLongProps, 100f*nLongProps/watchHisto.sum);
	writefln("c long confls:    %#10s (%#4.1f %% of watches)", nLongConfls, 100f*nLongConfls/watchHisto.sum);
	writefln("c clauses learnt: %#10s (%#4.1f %% shortened by otf)", nLearnt, 100f*nLitsOtfRemoved/nLitsLearnt);
	writefln("c xor results:    %#10s (%#4.1f %% units)", nXorUnits+nXorEqus, 100f*nXorUnits/(nXorUnits+nXorEqus));
	writefln("c lazy hyperBins: %#10s", nHyperBinary);

	writefln("c ============================ time stats =============================");
	auto total = Clock.currAppTick;
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
