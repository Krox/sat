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

	private this(uint i)
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
	private Array!int out2in; // -1 for for eliminated/fixed variables after renumber
	private Array!int in2out;
	private Array!Lit assign; // outer variables: undef / elim / fixed
	private Array!Lit equ;

	private Array!(Lit delegate(int)) extensionDelegate;
	private Array!int extensionVariable;

	int varCountInner() const @property { return cast(int)in2out.length; }
	int varCountOuter() const @property { return cast(int)out2in.length; }

	this(int n)
	{
		assign.resize(n, Lit.undef);
		equ.resize(n, Lit.undef);

		out2in.resize(n);
		in2out.resize(n);
		for(int i = 0; i < n; ++i)
			out2in[i] = in2out[i] = i;
	}

	Lit toInner(Lit l)
	{
		assert(l.proper);
		assert(out2in[l.var] != -1);
		return Lit(out2in[l.var], l.sign);
	}

	Lit toOuter(Lit l)
	{
		assert(l.proper);
		return Lit(in2out[l.var], l.sign);
	}

	/** Lit.zero/one/undef/elim */
	Lit valueOuter(Lit l)
	{
		if(assign[l.var].fixed)
			return assign[l.var]^l.sign;
		else
			return assign[l.var];
	}

	/** ditto */
	Lit valueInner(Lit l)
	{
		return valueOuter(toOuter(l));
	}

	void eliminateVariableOuter(int v, Lit delegate(int v) dg)
	{
		assert(assign[v] == Lit.undef);
		assign[v] = Lit.elim;
		extensionDelegate.pushBack(dg);
		extensionVariable.pushBack(v);
	}

	private Lit equEval(int v)
	{
		assert(equ[v].proper);
		return assign[equ[v].var]^equ[v].sign;
	}

	void setEquivalenceInner(Lit lit, Lit base)
	{
		lit = toOuter(lit);
		base = toOuter(base);

		assert(equ[lit.var] == Lit.undef);
		equ[lit.var] = base^lit.sign;
		eliminateVariableOuter(lit.var, &equEval);
	}

	/** return false, if the literal was already set */
	bool setLiteralInner(Lit l)
	{
		l = toOuter(l);

		if(assign[l.var] == (Lit.one^l.sign))
			return false;
		else if(assign[l.var] == (Lit.zero^l.sign))
			throw new Unsat;
		else
			assert(assign[l.var] == Lit.undef);

		assign[l.var] = Lit.one^l.sign;
		return true;
	}

	void renumber()
	{
		int k = 0;
		for(int i = 0; i < varCountOuter; ++i)
			if(assign[i] == Lit.undef)
				out2in[i] = k++;
			else
				out2in[i] = -1;

		in2out.resize(k);
		for(int i = 0; i < varCountOuter; ++i)
			if(out2in[i] != -1)
				in2out[out2in[i]] = i;
	}

	void extend()
	{
		while(!extensionVariable.empty)
		{
			int v = extensionVariable.popBack;
			Lit lit = extensionDelegate.popBack()(v);
			assert(lit.fixed && assign[v] == Lit.elim);
			assign[v] = lit;
		}
	}

	bool complete() const
	{
		for(int i = 0; i < varCountOuter; ++i)
			if(assign[i] == Lit.undef)
				return false;
		return true;
	}

	void writeAssignment() const
	{
		writef("v");
		for(int i = 0; i < varCountOuter; ++i)
		{
			if(!assign[i].fixed)
				throw new Exception("tried to output an incomplete assignment");
			writef(" %s", Lit(i, assign[i].sign));
		}
		writefln(" 0");
	}

	bool isSatisfiedOuter(const(Lit)[] c) const
	{
		foreach(l; c)
			if((assign[l.var]^l.sign) == Lit.one)
				return true;
		return false;
	}
}
