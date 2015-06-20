module sat.assignment;

private import std.stdio;
private import jive.array;

struct Lit
{
	uint toInt;
	alias toInt this; // TODO: remove this to avoid int<->Lit confusion
	static assert(Lit.sizeof == uint.sizeof);
	// NOTE: don't use std.bitmanip:bitfields. The asserts it contains are more annoying than helpful

	this(uint v, bool s)
	{
		toInt = (v<<1) | s;
	}

	this(uint i)
	{
		toInt = i;
	}

	uint var() const @property
	{
		return toInt >> 1;
	}

	void var(uint v) @property
	{
		toInt = (toInt & 1) | (v << 1);
	}

	bool sign() const @property
	{
		return toInt & 1;
	}

	void sign(bool s) @property
	{
		toInt = (toInt & ~1) | s;
	}

	Lit neg() const @property
	{
		return Lit(toInt ^ 1);
	}

	Lit opBinary(string op)(bool r) const
		if(op == "^")
	{
		return Lit(toInt^r);
	}

	int toDimacs() const @property
	{
		if(sign)
			return -(var+1);
		else
			return var+1;
	}

	string toString() const @property
	{
		switch(this.toInt)
		{
			case undef: return "undef";
			case elim: return "eliminated";
			case one: return "true";
			case zero: return "false";
			default: return to!string(toDimacs);
		}
	}

	static Lit fromDimacs(int x)
	{
		if(x > 0)
			return Lit(x-1, false);
		else
			return Lit(-x-1, true);
	}

	static enum Lit undef = Lit(-1, true);
	static enum Lit elim = Lit(-1, false);
	static enum Lit one = Lit(-2, false);
	static enum Lit zero = Lit(-2, true);
	static assert(one.fixed);
	static assert(zero.fixed);

	bool fixed() const @property
	{
		return (toInt&~1) == -4;
	}

	bool proper() const @property
	{
		return (toInt & (1U<<31)) == 0;
	}
}

class Unsat : Exception
{
	this()
	{
		super("answer is unsat");
	}
}

final class Assignment
{
	private Array!Lit assign; // undef / elim / fixed
	private Array!Lit equ;

	private Array!(Lit delegate()) extensionDelegate; // null for equivalences
	private Array!int extensionVariable;

	int varCount() const @property { return cast(int)assign.length; }

	this(int n)
	{
		assign.resize(n, Lit.undef);
		equ.resize(n, Lit.undef);
	}

	/** Lit.zero/one/undef/elim */
	Lit opIndex(Lit l)
	{
		if(!l.proper)
			return l;
		if(assign[l.var].fixed)
			return assign[l.var]^l.sign;
		else
			return assign[l.var];
	}

	void eliminateVariable(int v, Lit delegate() dg)
	{
		assert(assign[v] == Lit.undef);
		assign[v] = Lit.elim;
		extensionDelegate.pushBack(dg);
		extensionVariable.pushBack(v);
	}

	void setEquivalence(Lit lit, Lit base)
	{
		assert(equ[lit.var] == Lit.undef);
		equ[lit.var] = base^lit.sign;
		assign[lit.var] = Lit.elim;
		extensionDelegate.pushBack(null);
		extensionVariable.pushBack(lit.var);
	}

	/** return false, if the literal was already set */
	bool setLiteral(Lit l)
	{
		if(assign[l.var] == (Lit.one^l.sign))
			return false;
		else if(assign[l.var] == (Lit.zero^l.sign))
			throw new Unsat;
		else
			assert(assign[l.var] == Lit.undef);

		assign[l.var] = Lit.one^l.sign;
		return true;
	}

	void extend()
	{
		while(!extensionVariable.empty)
		{
			int v = extensionVariable.popBack;
			auto dg = extensionDelegate.popBack;

			assert(assign[v] == Lit.elim);

			if(dg is null) // equivalence
				assign[v] = assign[equ[v].var]^equ[v].sign;
			else // non-trivial extension
				assign[v] = dg();

			assert(assign[v].fixed);
		}
	}

	bool complete() const
	{
		for(int i = 0; i < varCount; ++i)
			if(assign[i] == Lit.undef)
				return false;
		return true;
	}

	void writeAssignment() const
	{
		writef("v");
		for(int i = 0; i < varCount; ++i)
		{
			if(!assign[i].fixed)
				throw new Exception("tried to output an incomplete assignment");
			writef(" %s", Lit(i, assign[i].sign));
		}
		writefln(" 0");
	}

	bool isSatisfied(Lit a) const
	{
		return (assign[a.var]^a.sign) == Lit.one;
	}

	bool isSatisfied(Lit a, Lit b) const
	{
		return isSatisfied(a) || isSatisfied(b);
	}

	bool isSatisfied(Lit a, Lit b, Lit c) const
	{
		return isSatisfied(a) || isSatisfied(b) || isSatisfied(c);
	}

	bool isSatisfied(const(Lit)[] c) const
	{
		foreach(l; c)
			if(isSatisfied(l))
				return true;
		return false;
	}
}
