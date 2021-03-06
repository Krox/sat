module sat.xor;

private import core.bitop : popcnt;
private import std.stdio;
private import std.range;
private import std.algorithm;

import jive.array;
import sat.flatset;

import sat.sat;
import sat.stats;

void solveXor(Sat sat)
{
	swXor.start();
	scope(exit)
		swXor.stop();

	auto finder = new XorSolver(sat);
	finder.search();
	if(finder.clauses.length == 0)
		return;
	auto nClauses = finder.clauses.length;

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
	Array!(FlatSet!int) occ;

	this(Sat sat)
	{
		this.sat = sat;
		occ.resize(sat.varCount);
	}

	void addClause(XorClause c)
	{
		foreach(l; c.lits)
			occ[l].pushBack(cast(int)clauses.length);
		clauses.pushBack(move(c));
	}

	/**
	 *  returns true if a is a subclause of b^signs.
	 *  assumes both clauses are
	 */
	bool subclause(const(Lit)[] a, const(Lit)[] b, uint signs)
	{
		while(true)
		{
			if(a.length > b.length)
				return false;
			if(a.length == 0)
				return true;
			if(a.front == (b.front^((signs&1) != 0)))
				a.popFront;

			b.popFront;
			signs /= 2;
		}
	}

	/** search for xor clauses encoded in the cnf clauses */
	// TODO: enable the searcher to find use (virtual) binary clauses
	void search()
	{
		// one watch per clause, one list per variable (not per literal!)
		Array!(Array!CRef) watches;
		watches.resize(sat.varCount);
		foreach(i, ref c; sat.clauses)
			if(c.length && c.length <= 6)
			{
				sort(sat.clauses[i][]);
				sat.clauses[i].unmark;
				watches[c[0].var].pushBack(i);
			}

		outer: foreach(i, ref c; sat.clauses)
			if(c.length && c.length <= 6)
				if(!c.marked)
				{
					inner: for(uint signs = 1; signs < (1 << c.length); ++signs)
						if(popcnt(signs) % 2 == 0)
						{
							foreach(Lit l; c[])
								foreach(k; watches[l.var])
									if(subclause(sat.clauses[k][], c[], signs))
									{
										if(sat.clauses[k].length == c.length)
											sat.clauses[k].mark();
										continue inner;
									}

							continue outer;
						}

					addClause(XorClause(c));
				}
	}

	/** do Gaussian elimination */
	void gauss()
	{
		for(int i = 0; i < clauses.length; ++i)
		{
			if(clauses[i].length == 0)
				continue;

			// choose pivot with fewest occurences
			int pivot = clauses[i][0];
			foreach(p; clauses[i][][1..$])
				if(occ[p].length < occ[pivot].length)
					pivot = p;

			foreach(j; occ[pivot])
				if(i != j)
				{
					assert(pivot in clauses[j]);
					clauses[j] += clauses[i];
				}

			if(!occ[pivot].remove(i))
				assert(false);

			foreach(l; clauses[i])
				if(l != pivot)
					occ[l] = occ[l].symmetricDifference(occ[pivot]);

			occ[pivot].resize(1);
			occ[pivot][0] = i;
		}

	}

	/** put unit clauses and equivalences back into the cnf problem */
	void implement()
	{
		foreach(ref c, ref bool rem; clauses.prune)
			switch(c.length)
			{
				case 0:
					if(c.rhs)
					{
						sat.addEmpty();
						++nXorUnits;	// technically its not a unit, but a separate counter is stupid
					}

					rem = true;
					break;

				case 1:
					sat.addClause(Lit(c[0], !c.rhs));
					++nXorUnits;
					rem = true;
					break;

				case 2:
					if(occ[c[0]].length != 1)
						swap(c[0],c[1]);
					assert(occ[c[0]].length == 1); // make sure the removed variable does not appear in any other clause (i.e. it is pivot)
					sat.addClause(Lit(c[0], false)^true, Lit(c[1], c.rhs));
					sat.addClause(Lit(c[0], false), Lit(c[1], c.rhs)^true);
					++nXorEqus;
					rem = true;
					break;

				default:
					break;
			}

		outer: foreach(ref c; clauses)
		{
			for(int i = 0; i < c.length; ++i)
				if(occ[c[i]].length == 1)
				{
					int pivot = c[i];
					for(int j = i; j >= 1; --j)
						c[j] = c[j-1];
					c[0] = pivot;
					continue outer;
				}
			throw new Exception("xor system not fully gaussed");
		}

		sort!"a.lits[1..$] < b.lits[1..$]"(clauses[]);

		for(int i = 1; i < clauses.length; ++i)
			if(clauses[i-1].lits[][1..$] == clauses[i].lits[][1..$])
			{
				sat.addClause(Lit(clauses[i-1][0], false)^true, Lit(clauses[i][0], clauses[i-1].rhs^clauses[i].rhs));
				sat.addClause(Lit(clauses[i-1][0], false), Lit(clauses[i][0], clauses[i-1].rhs^clauses[i].rhs)^true);
				++nXorEqus;
			}
	}

	/** check occ lists, for debugging */
	void check()
	{
		size_t count = 0;

		for(int l = 0; l < occ.length; ++l)
		{
			count += occ[l].length;
			foreach(i; occ[l])
				assert(l in clauses[i]);
		}

		writefln("c checked (# = %s)", count);

		foreach(ref c; clauses)
			count -= c.length;

		assert(count == 0);
	}
}
