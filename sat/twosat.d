module sat.twosat;

private import std.stdio;
import std.algorithm : min, sort;
import jive.array;
import sat.sat;

void solve2sat(Sat sat)
{
	Array!(Array!Lit) g;
	Array!bool visited;
	Array!uint back;
	Array!Lit stack;
	int cnt = 0;
	Array!Lit comp;

	void dfs(Lit v)
	{
		if(visited[v.toInt])
			return;
		visited[v.toInt] = true;
		int x = back[v.toInt] = cnt++;

		stack.pushBack(v);

		foreach(w; g[v.toInt])
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

	g.resize(sat.varCount*2);

	int nBins = false;
	foreach(ref c; sat.clauses)
		if(c.length == 2)
		{
			++nBins;
			g[c[0].neg.toInt].pushBack(c[1]);
			g[c[1].neg.toInt].pushBack(c[0]);
		}

	if(nBins == 0)
		return;

	back.resize(sat.varCount*2);
	visited.resize(sat.varCount*2);

	for(int v = 0; v < sat.varCount; ++v)
	{
		dfs(Lit(v,false));
		dfs(Lit(v,true));
	}

	int nProps = sat.propagate();
	writefln("c tarjan on %s binary clauses removed %s vars", nBins, nProps);
}
