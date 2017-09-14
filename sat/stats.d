module sat.stats;

/**
 * global variables for configuration and statistics;
 */

import std.stdio;
import std.datetime : Clock, StopWatch;
import std.algorithm;

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
long nBinaryReduction;

struct config
{
	static:
	// features of the solver
	bool binarySubsume = true;
	int otf = 2;
	bool hyperBinary = true;
	bool xor = true;

	// statistic output
	bool watchStats = false;
}

void writeStats()
{
	if(config.watchStats)
	{
		writefln("c ========================== watchlist sizes ==========================");
		watchHisto.write;
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
	writefln("c trans binary:   %#10s", nBinaryReduction);

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

struct Histogram
{
	enum limit = 21;

	long[limit] hist;
	long count = 0;
	long countHigh = 0;
	long sum = 0;
	long max = long.min;

	void add(long x)
	{
		assert(x >= 0);
		count += 1;
		sum += x;
		max = std.algorithm.max(max, x);

		if(x >= limit)
			countHigh += 1;
		else
			hist[x] += 1;
	}

	double avg() const nothrow @property @safe
	{
		return cast(double)sum / count;
	}

	void write() const
	{
		foreach(i, c; hist)
			writefln("c %s:\t%s", i, c);
		if(countHigh)
			writefln("c >:\t%s", countHigh);
		writefln("c all:\t%s", count);
		writefln("c avg = %s", avg);
	}
}
