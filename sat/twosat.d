module sat.twosat;

private import std.stdio;
private import std.algorithm : min, sort;
import jive.array;

import sat.sat;

/**
 * explicit solving of the two-sat sub-problem. I.e. looking for equivalent
 * variables. very fast (linear in problem size), implemented using tarjan's
 * algorithm for stongly connected components.
 */
class TwoSat
{
	private Sat sat;
	private Array!bool visited;
	private Array!uint back;
	private Array!Lit stack;
	private int cnt = 0;
	private Array!Lit comp;
	private Array!Lit equ;
	private int nComps = 0; // number of SCC's

	private void dfs(Lit v)
	{
		if(visited[v.toInt])
			return;
		visited[v.toInt] = true;

		int x = back[v.toInt] = cnt++;

		stack.pushBack(v);

		foreach(w; sat.bins[v.neg])
		{
			dfs(w);
			x = min(x, back[w.toInt]);
		}

		if(x < back[v.toInt])
		{
			back[v.toInt] = x;
			return;
		}

		comp.resize(0);

		while(true)
		{
			Lit t = stack.popBack();
			back[t.toInt] = 999999999;
			comp.pushBack(t);
			if(t == v)
				break;
		}

		sort(comp[]);
		if(comp[0].sign == true)
			return;

		if(comp.length >= 2 && comp[0] == comp[1].neg)
			throw new Unsat;

		//if(comp.length > 1)
		//	writefln("%s", comp[]);

		foreach(l; comp[1..$])
			sat.assign.setEquivalence(sat.toOuter(l), sat.toOuter(comp[0]));

		foreach(l; comp[])
		{
			assert(equ[l.var] == Lit.undef);
			equ[l.var] = Lit(nComps, l.sign);
		}

		nComps++;
	}

	void run()
	{
		swTarjan.start();
		scope(exit)
			swTarjan.stop();

		// initialize / resize datastructures
		cnt = 0;
		nComps = 0;
		assert(stack.empty);
		back.assign(sat.varCount*2, 0);
		visited.assign(sat.varCount*2, false);
		equ.assign(sat.varCount, Lit.undef);

		// run tarjan
		for(int i = 0; i < sat.varCount*2; ++i)
			dfs(Lit(i));

		// no equivalences -> quit
		if(nComps == sat.varCount)
			return;

		sat.renumber(equ[], nComps, true);
	}

	this(Sat sat)
	{
		this.sat = sat;
	}
}
