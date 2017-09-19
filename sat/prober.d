module sat.prober;

/**
 * Failed-literal probing. Intended as a light-weight top-level simplification.
 */

import std.stdio;
import std.algorithm : move, swap;
import jive.array;
import jive.bitarray;
import algo.graph;
import sat.sat;

struct Reason
{
	enum
	{
		nil = 0x0000_0000_U,
		binary = 0x4000_0000_U,
		clause = 0x8000_0000_U,
	}

	enum dataMask = 0x3FFF_FFFF_U;
	enum typeMask = 0xC000_0000_U;

	uint data = nil;

	enum unit = fromInt(0);
	enum branch = fromInt(1);

	uint type() const nothrow @property @safe
	{
		return data & typeMask;
	}

	CRef n() const nothrow @property @safe
	{
		assert(type == clause);
		return CRef(data & dataMask);
	}

	Lit lit2() const nothrow @property @safe
	{
		assert(type == binary);
		return Lit(data & dataMask);
	}

	static enum Reason undef = Reason.init;

	this(Lit lit2)
	{
		assert((lit2.toInt & typeMask) == 0);
		this.data = lit2.toInt | binary;
	}

	this(CRef n)
	{
		assert((n.toInt & typeMask) == 0);
		this.data = n.toInt | clause;
	}

	static Reason fromInt(uint d)
	{
		Reason r;
		r.data = d;
		return r;
	}
}

final class Prober
{
	Sat sat;

	BitArray assign;
	Array!Reason reason; // only valid for assigned variables
	Array!(Array!CRef) watches; // watches into long clauses
	Array!Lit stack; // trail of set variables (including top-level units)

	private BitArray seen;
	private const(Lit)[] conflict;

	private this(Sat sat)
	{
		swProber.start();
		scope(exit)
			swProber.stop();

		this.sat = sat;

		assign.resize(2*sat.varCount);
		reason.resize(sat.varCount);
		watches.resize(2*sat.varCount);
		seen.resize(sat.varCount);

		// add long clauses (i.e. create watches)
		foreach(i, ref c; sat.clauses)
		{
			assert(c.length >= 3); // such should have been converted to implicit clauses
			watches[c[0]].pushBack(i);
			watches[c[1]].pushBack(i);
		}

		// propagate unit clauses. NOTE: do this after adding long clauses to get consistent watches
		foreach(l; sat.units)
		{
			assert(l.proper);
			if(assign[l]) // already set -> do nothing
				continue;
			if(assign[l.neg] || !propagate(l, Reason.unit)) // conflict -> UNSAT
			{
				sat.addEmpty();
				return;
			}
		}

		// mark everything as top-level
		foreach(l; stack[])
			reason[l.var] = Reason.unit;
	}

	/** unroll all assignments up to the top n */
	void unroll(size_t n)
	{
		assert(stack.length >= n);
		while(stack.length > n)
		{
			assert(assign[stack.back] == true);
			assert(assign[stack.back.neg] == false);
			assign[stack.popBack] = false;
		}
	}

	/* set a (previously unset) literal x with reason r */
	private void set(Lit x, Reason r)
	{
		assert(assign[x] == false);
		assert(assign[x.neg] == false);
		assign[x] = true;
		stack.pushBack(x);
		reason[x.var] = r;
	}

	/**
	 * Set a (previously unset) variable and propagate binaries.
	 * Returns false on conflict.
	 */
	private bool propagateBinary(Lit root, Reason reason)
	{
		assert(!assign[root] && !assign[root.neg]);

		auto pos = stack.length();
		set(root, reason);

		while(pos != stack.length)
		{
			auto x = stack[pos++];

			// propagate binary clauses
			foreach(Lit y; sat.bins[x.neg])
			{
				// already set correct -> do nothing
				if(assign[y])
					continue;

				// already set wrong -> conflict
				if(assign[y.neg])
				{
					static Lit[2] conf;
					conf[0] = x.neg;
					conf[1] = y;
					conflict = conf[];
					return false;
				}

				// not set at all -> propagate
				set(y, Reason(x.neg));
			}
		}

		return true;
	}

	/**
	 * Set a (previously unset) variable and propagate everything.
	 * Returns dominator on conflict, Lit.undef if all is fine.
	 */
	private bool propagate(Lit _x, Reason reason)
	{
		size_t pos = stack.length;
		assert(!assign[_x] && !assign[_x.neg]);
		if(!propagateBinary(_x, reason))
			return false;

		while(pos != stack.length)
		{
			auto x = stack[pos++];

			// propagate long clauses
			outer: foreach(i, ref bool rem; watches[x.neg].prune)
			{
				Lit[] c = sat.clauses[i][];

				// move current variable to position 1
				// (so that c[0] is the potentially propagated one)
				if(x.neg == c[0])
					swap(c[0], c[1]);
				assert(x.neg == c[1]);

				// other watch satisfied -> do nothing
				if(assign[c[0]])
					continue outer;

				// look for other satisfied/undef literals to move the watch
				foreach(ref y; c[2..$])
					if(!assign[y.neg])
					{
						swap(c[1], y);
						watches[c[1]].pushBack(i);
						rem = true;
						continue outer;
					}

				// all literals false -> conflict
				if(assign[c[0].neg])
				{
					conflict = c;
					return false;
				}

				// else -> we found a propagation
				if(!propagateBinary(c[0], Reason(i)))
					return false;
			}
		}

		return true;
	}

	/** Common (negative-)dominator of (negative-)assigned literals. */
	Lit dominator(const(Lit)[] lits) /*const*/
	{
		assert(lits.length >= 2); // pointless to do otherwise

		seen.reset();
		int count = 0;

		foreach(l; lits)
		{
			assert(assign[l.neg] && !assign[l]);
			assert(!seen[l.var]);
			if(reason[l.var] == Reason.unit) // ignore top-level units
				continue;
			++count;
			seen[l.var] = true;
		}

		assert(count > 0);
		if(count == 0)
			return Lit.zero;

		foreach_reverse(x; stack[])
		{
			if(!seen[x.var])
				continue;

			if(--count == 0)
				return x.neg;

			auto r = reason[x.var];

			if(r.type == Reason.binary)
			{
				auto y = reason[x.var].lit2;

				if(!seen[y.var])
				{
					++count;
					seen[y.var] = true;
				}
			}
			else if(r.type == Reason.clause)
			{
				foreach(y; sat.clauses[r.n][][1..$])
				{
					if(reason[y.var] == Reason.unit)
						continue;
					if(!seen[y.var])
					{
						++count;
						seen[y.var] = true;
					}
				}
			}
			else assert(false);
		}

		assert(false);
	}

	/**
	 * Run failed-literal probing.
	 * This can add empty/unit/binary clauses to the Sat instance
	 */
	private void run()
	{
		swProber.start();
		scope(exit)
			swProber.stop();

		if(sat.contradiction)
			return;

		auto top = TopOrder(sat.implicationGraph);
		auto done = BitArray(2*sat.varCount);
		foreach(x; top.verts[])
		{
			auto lit = Lit(x);

			// skip assigned variables and marked literals
			if(assign[lit] || assign[lit.neg] || done[lit])
				continue;

			// only consider roots of binary implication graph
			if(sat.bins[lit.neg].empty || !sat.bins[lit].empty)
				continue;

			auto mark = stack.length;
			if(propagate(lit, Reason.branch))
			{
				// no conflict -> mark others as done
				foreach(l; stack[mark..$])
					done[l] = true;
				unroll(mark);
			}
			else
			{
				// conflict -> analyze and add new unit
				++nFailedLits;
				auto d = dominator(conflict);
				unroll(mark);

				if(!propagate(d, Reason.unit))
				{
					sat.addEmpty;
					return;
				}
				nFailedUnits += stack.length - mark;

				// mark new units as top-level
				foreach(l; stack[mark..$])
					reason[l.var] = Reason.unit;
			}
		}
	}
}

/** do unit propagation only */
void runUnitPropagation(Sat sat)
{
	auto p = new Prober(sat);
	sat.units = p.stack.move;
	delete p;
}

/** do full failed literal probing */
void runProber(Sat sat)
{
	auto p = new Prober(sat);
	p.run;
	sat.units = p.stack.move;
	delete p;
}
