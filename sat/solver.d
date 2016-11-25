module sat.solver;

private import std.stdio;

private import sat.sat, sat.searcher, sat.twosat, sat.simplify;

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
Solution solve(Sat sat)
{
	Solution sol;
	long lastCleanup = 0;
	// this is cheap, so just run it before starting up anything sophisticated
	new TwoSat(sat).run();
	sat.cleanup();

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

		bool solved = searcher.run(luby(i)*100, sol);

		if(solved)
			break;

		while(sat.units.length >= 100) // TODO: tweak strategy (after optimizing searcher startup time)
		{
			//sat.clauses.histogram(true).write();
			sat.clean(1000);
			//sat.clauses.histogram(true).write();

			lastCleanup = nConflicts;
			delete searcher;

			sat.cleanup;

			new TwoSat(sat).run();
			sat.cleanup;

			if(config.binarySubsume)
			{
				simplify(sat);
				sat.cleanup;
			}

			sat.writeStatsLine();
		}
	}

	if(sat.contradiction)
		return null;
	else
	{
		assert(sol !is null),
		assert(sol.complete);
		return sol;
	}
}
