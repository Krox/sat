module sat.types;

import std.format;

struct lbool
{
	@nogc: nothrow: pure: @safe:

	byte val = 2; // 0=false, 1=true, 2=undef

	this(bool b)
	{
		val = b;
	}

	private this(byte v) pure nothrow @safe
	{
		val = v;
	}

	bool opCast(T)() const pure nothrow @safe
		if(is(T == bool))
	{
		return val == 1;
	}

	lbool opUnary(string op)() const pure nothrow @safe
		if(op == "~")
	{
		return lbool((val^1)&~(val>>1));
	}

	bool opEquals(bool b) const pure nothrow @safe
	{
		return val == cast(byte)b;
	}

	bool opEquals(lbool b) const pure nothrow @safe
	{
		return val == b.val;
	}

	static enum lbool zero = lbool(0);
	static enum lbool one = lbool(1);
	static enum lbool undef = lbool(2);
}

static assert(lbool.sizeof == 1);
static assert(~lbool.one == lbool.zero);
static assert(~lbool.zero == lbool.one);
static assert(~lbool.undef == lbool.undef);
static assert(lbool(true) == lbool.one);
static assert(lbool(false) == lbool.zero);
static assert(lbool(true) == true);
static assert(lbool(false) == false);
static assert(lbool.undef != false);
static assert(lbool.undef != true);
static assert(lbool.init == lbool.undef);

struct Lit
{
	@nogc: nothrow: pure: @safe:

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
