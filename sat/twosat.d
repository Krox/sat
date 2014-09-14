module sat.twosat;

private import std.stdio;
import std.algorithm : min, sort;
import jive.array;
import sat.sat;

class solve2sat
{
	private Sat sat;
	private Array!bool visited;
	private Array!uint back;
	private Array!Lit stack;
	private int cnt = 0;
	private Array!Lit comp;
	private int nProps = 0;

	private void dfs(Lit v)
	{
		if(visited[v.toInt])
			return;
		visited[v.toInt] = true;
		sat.binaryNew[v.neg.toInt] = false;

		int x = back[v.toInt] = cnt++;

		stack.pushBack(v);

		foreach(w; sat.bins(v.neg))
		{
			dfs(w);
			x = min(x, back[w.toInt]);
		}

		if(x < back[v.toInt])
		{
			back[v.toInt] = x;
			return;
		}

		while(true)
		{
			Lit t = stack.popBack();
			back[t.toInt] = 999999999;
			comp.pushBack(t);
			if(t == v)
				break;
		}

		sort(comp[]);
		if(comp[0].sign == false)
			foreach(l; comp[1..$])
				sat.setEquivalence(l, comp[0]);
		comp.resize(0);
	}

	private void run()
	{
		cnt = 0;
		assert(comp.empty);
		assert(stack.empty);
		back.assign(sat.varCount*2, 0);
		visited.assign(sat.varCount*2, false);

		for(int v = 0; v < sat.varCount; ++v)
		{
			if(sat.binaryNew[Lit(v, true)])
				dfs(Lit(v,false));
			if(sat.binaryNew[Lit(v, false)])
				dfs(Lit(v,true));
		}

		sat.binaryAnyNew = false;
		nProps += sat.propagate();
	}

	private this(Sat sat)
	{
		this.sat = sat;
	}

	static void opCall(Sat sat)
	{
		if(!sat.binaryAnyNew)
			return;

		auto x = new solve2sat(sat);
		while(sat.binaryAnyNew)
			x.run();

		if(x.nProps)
			writefln("c tarjan removed %s vars", x.nProps);
	}
}
