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

	scope(exit)
		sat.writeStatsFooter();

	Searcher searcher = null;
	for(int i = 1; ; ++i)
	{
		if(searcher is null)
			searcher = new Searcher(sat);

		// run the CDCL searcher
		sat.writeStatsLine();
		bool solved = searcher.run(luby(i)*100, sol);

		if(solved)
			break;

		// occasionally do some simplification and cleaning
		// TODO: tweak policy when to do this and how much clause cleaning to do
		while(sat.units.length >= 100 || nConflicts >= lastCleanup+1000)
		{
			lastCleanup = nConflicts;
			delete searcher;

			// implement units, replace equivalent literals and renumber everything
			sat.cleanup;
			new TwoSat(sat).run();
			sat.cleanup;

			// some simplification based on subsumption
			if(config.binarySubsume)
			{
				simplify(sat);
				sat.cleanup;
			}

			// remove some learnt clauses
			sat.clean(nConflicts/3);
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
