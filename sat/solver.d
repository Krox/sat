module sat.solver;

private import std.stdio;

private import sat.sat, sat.searcher, sat.twosat;

private import core.bitop: bsr, popcnt;


/** luby sequence, used as restart strategy */
private int luby(int i)
{
	if(popcnt(i+1) == 1)
		return (i+1)/2;
	else
		return luby(i-(1<<bsr(i))+1);
}

/**
 *  solves a sat problem.
 *  afterwards, sat will either have a contradiction or a solution
 */
void solve(Sat sat)
{
	long lastCleanup = 0;
	// this is cheap, so just run it before starting up anything sophisticated
	new TwoSat(sat).run();

	sat.writeStatsHeader();
	sat.writeStatsLine();

	scope(exit)
		sat.writeStatsFooter();

	Searcher searcher = null;
	for(int i = 1; ; ++i)
	{
		// run the CDCL searcher
		if(searcher is null)
			searcher = new Searcher(sat);
		bool solved = searcher.run(luby(i)*100);

		if(solved)
			break;

		while(sat.units.length >= 100) // TODO: tweak strategy (after optimizing searcher startup time)
		{
			lastCleanup = nConflicts;
			delete searcher;
			sat.cleanup;
			new TwoSat(sat).run();

			sat.writeStatsLine();
		}
	}

	if(!sat.contradiction)
	{
		sat.cleanup;
		assert(sat.varCount == 0);
		sat.solution.extend();
	}
}
