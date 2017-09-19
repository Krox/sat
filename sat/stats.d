module sat.stats;

/**
 * global variables for configuration and statistics;
 */

import std.stdio;
import core.time;
import std.datetime : StopWatch;
import std.algorithm;

StopWatch swTarjan, swCleanup, swProber;
StopWatch swSubsume, swSubsumeBin, swXor;
StopWatch swSolver, swSolverInit;
StopWatch swTmp1, swTmp2, swTmp3, swTmp4;

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
long nFailedLits;
long nFailedUnits;

struct config
{
	static:
	// features of the solver
	bool binarySubsume = true;
	int otf = 2;
	bool lhbr = true;
	bool xor = true;
	int probing = 2;

	// statistic output
	bool watchStats = false;
}

MonoTime startTime;

static this()
{
	startTime = MonoTime.currTime;
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
	writefln("c failed lits:    %#10s (%4.1f units each)", nFailedLits, 1f*nFailedUnits/nFailedLits);
	writefln("c trans binary:   %#10s", nBinaryReduction);

	auto timeTarjan = swTarjan.peek.msecs/1000.0f;
	auto timeCleanup = swCleanup.peek.msecs/1000.0f;
	auto timeProber = swProber.peek.msecs/1000.0f;
	auto timeXor = swXor.peek.msecs/1000.0f;
	auto timeSubsume = swSubsume.peek.msecs/1000.0f;
	auto timeSubsumeBin = swSubsumeBin.peek.msecs/1000.0f;
	auto timeSolverInit = swSolverInit.peek.msecs/1000.0f;
	auto timeSolver = swSolver.peek.msecs/1000.0f;
	auto timeTmp1 = swTmp1.peek.msecs/1000.0f;
	auto timeTmp2 = swTmp2.peek.msecs/1000.0f;
	auto timeTmp3 = swTmp3.peek.msecs/1000.0f;
	auto timeTmp4 = swTmp4.peek.msecs/1000.0f;
	auto timeTotal = (MonoTime.currTime - startTime).total!"msecs"/1000.0f;

	writefln("c ============================ time stats =============================");
	writefln("c tarjan     %#6.2f s (%#4.1f %%)", timeTarjan, 100f*timeTarjan/timeTotal);
	writefln("c cleanup    %#6.2f s (%#4.1f %%)", timeCleanup, 100f*timeCleanup/timeTotal);
	writefln("c prober     %#6.2f s (%#4.1f %%)", timeProber, 100f*timeProber/timeTotal);
	writefln("c xor        %#6.2f s (%#4.1f %%)", timeXor, 100f*timeXor/timeTotal);
	writefln("c subsume    %#6.2f s (%#4.1f %%)", timeSubsume, 100f*timeSubsume/timeTotal);
	writefln("c subsumeBin %#6.2f s (%#4.1f %%)", timeSubsumeBin, 100f*timeSubsumeBin/timeTotal);
	writefln("c solverInit %#6.2f s (%#4.1f %%)", timeSolverInit, 100f*timeSolverInit/timeTotal);
	writefln("c solver     %#6.2f s (%#4.1f %%)", timeSolver, 100f*timeSolver/timeTotal);
	if(timeTmp1 != 0) writefln("c tmp 1      %#6.2f s (%#4.1f %%)", timeTmp1, 100f*timeTmp1/timeTotal);
	if(timeTmp2 != 0) writefln("c tmp 2      %#6.2f s (%#4.1f %%)", timeTmp2, 100f*timeTmp2/timeTotal);
	if(timeTmp3 != 0) writefln("c tmp 3      %#6.2f s (%#4.1f %%)", timeTmp3, 100f*timeTmp3/timeTotal);
	if(timeTmp4 != 0) writefln("c tmp 4      %#6.2f s (%#4.1f %%)", timeTmp4, 100f*timeTmp4/timeTotal);
	writefln("c total      %#6.2f s", timeTotal);
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
