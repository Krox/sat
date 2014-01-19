module sat.xor;

import jive.array;
import jive.flatset;
import jive.unionfind;
private import core.bitop : popcnt;
private import std.stdio;
private import std.range;
import sat.sat;

void solveXor(Sat sat)
{
	auto finder = new XorSolver(sat);
	finder.search();
	if(finder.clauses.length == 0)
		return;
	finder.gauss();
	finder.implement();
}

struct XorClause
{
	FlatSet!int lits;
	alias lits this;
	bool rhs;

	this(const ref Clause c)
	{
		rhs = popcnt(c.signs)%2 == 0;
		lits.reserve(c.length);
		foreach(l; c)
			lits.add(l.var);
	}

	void opAddAssign(ref XorClause c)
	{
		rhs = rhs != c.rhs;
		lits = lits.symmetricDifference(c.lits);
	}
}

final class XorSolver
{
	Sat sat;
	Array!XorClause clauses;

	this(Sat sat)
	{
		this.sat = sat;
	}

	void search()
	{
		Array!bool mark;
		mark.resize(sat.clauses.length);
		outer: foreach(ci, const ref c; sat.clauses)
			if(c.length >= 3 && c.length <= 6)
				if(!mark[ci])
				{
					uint sig = c.signs;
					for(uint i = 1; i < (1 << c.length); ++i)
						if(popcnt(i) % 2 == 0)
						{
							int j = sat.findClause(c, i);
							if(j == -1)
								continue outer;
							if(sat.clauses[j].length == c.length)
								mark[j] = true;
						}

					clauses.pushBack(XorClause(c));
				}
	}

	void gauss()
	{
		auto uf = UnionFind(sat.varCount);
		foreach(ref c; clauses)
			uf.join(c[]);

		auto comps = uf.components();

		writefln("c gaussing %s xors in %s components", clauses.length, comps[0]);

		auto blocks = Array!(Array!int)(comps[0]);
		foreach(int i, ref c; clauses)
			blocks[comps[1][c[0]]].pushBack(i);

		foreach(ref b; blocks)
			gauss(indexed(clauses[], b[]));
	}

	static void gauss(Clauses)(Clauses clauses)
		if(isRandomAccessRange!Clauses && is(ElementType!Clauses==XorClause))
	{
		foreach(ref c; clauses)
		{
			if(c.length == 0)
				continue;

			int pivot = c[0];
			foreach(ref d; clauses)
				if(&c != &d) // should use index-comparison instead, but std.range:indexed does not allow that
					if(pivot in d)
						d += c;
		}
	}

	void implement()
	{
		foreach(i, ref c; clauses)
			switch(c.length)
			{
				case 0:
					if(c.rhs)
						throw new Unsat;
					break;

				case 1:
					sat.setLiteral(Lit(c[0], !c.rhs));
					break;

				case 2:
					sat.setEquivalence(Lit(c[0], false), Lit(c[1], c.rhs));
					break;

				default:
					break;
			}
	}
}
