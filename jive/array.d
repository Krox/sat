module jive.array;

private import std.range : isInputRange, ElementType, hasLength;
private import std.algorithm : moveAll, move;

// TODO: maybe implement toString and something similar to idup
// TODO: figure out how to allow const-parameters for pushBack and alike (for value-type V)
// TODO: add a couple of @safe and nothrow attributes

/**
 *  pretty much the thing, STL called vector. never shrinks. value semantic.
 */
struct Array(V)
{
	//////////////////////////////////////////////////////////////////////
	/// constructors
	//////////////////////////////////////////////////////////////////////

	/** constructor for given length */
	this(size_t size)
	{
		buf = new V[size];
		count = size;
	}

	/** constructor for given length and init */
	this(size_t size, V val)
	{
		this(size);
		this[] = val;
	}

	this(V[] val)
	{
		this(val.length);
		this[][] = val[];
	}

	/** post-blit that does a full copy */
	this(this)
	{
		static import std.stdio	;// TODO: remove this
		if(length != 0)
		std.stdio.writefln("called copy-constructor on Array!%s of length %s", V.stringof, length);
		buf = buf.ptr[0..count].dup;
	}


	//////////////////////////////////////////////////////////////////////
	/// metrics
	//////////////////////////////////////////////////////////////////////

	/** check for emptiness */
	bool empty() const nothrow @property @safe
	{
		return count == 0;
	}

	/** number of elements */
	size_t length() const nothrow @property @safe
	{
		return count;
	}

	/** ditto */
	size_t opDollar() const nothrow @property @safe
	{
		return count;
	}

	/** number of elements this structure can hold without further allocations */
	size_t capacity() const nothrow @property @safe
	{
		return buf.length;
	}

	/** make sure this structure can contain given number of elements without further allocs */
	void reserve(size_t size)
	{
		if(size <= buf.length)
			return;

		auto newBuf = new V[size];
		moveAll(buf[], newBuf[0..buf.length]);
		buf = newBuf;
	}


	//////////////////////////////////////////////////////////////////////
	/// indexing
	//////////////////////////////////////////////////////////////////////

	/** indexing */
	ref V opIndex(size_t index) @safe
	{
		return buf.ptr[0..count][index];	// will use correct bounds-check
	}

	/** ditto */
	ref const(V) opIndex(size_t index) const @safe
	{
		return buf.ptr[0..count][index];	// will use correct bounds-check
	}

	/** default range */
	V[] opSlice() nothrow @safe
	{
		return buf.ptr[0..count];	// no bounds-check
	}

	/** ditto */
	const(V)[] opSlice() const nothrow @safe
	{
		return buf.ptr[0..count];	// no bounds-check
	}

	/** range */
	V[] opSlice(size_t start, size_t end) @safe
	{
		return buf.ptr[0..count][start..end];	// correct bounds-check
	}

	/** ditto */
	const(V)[] opSlice(size_t start, size_t end) const @safe
	{
		return buf.ptr[0..count][start..end];	// correct bounds-check
	}

	void opSliceAssign(V value) nothrow @safe
	{
		buf.ptr[0..count] = value;	// no bounds-check
	}

	void opSliceAssign(ref V value) nothrow @safe
	{
		buf.ptr[0..count] = value;	// no bounds-check
	}

	void opSliceAssign(V value, size_t a, size_t b) @safe
	{
		buf[a..b] = value;	// will use correct bounds-check
	}

	void opSliceAssign(ref V value, size_t a, size_t b) @safe
	{
		buf[a..b] = value;	// will use correct bounds-check
	}

	void opAssign(V[] vals)
	{
		resize(vals.length);
		buf[0..count] = vals[];
	}

	/** first element */
	ref V front() @property
	{
		return buf.ptr[0..count][0];	// will use correct bounds-check
	}

	/** ditto */
	ref const(V) front() const @property
	{
		return buf.ptr[0..count][0];	// will use correct bounds-check
	}

	/** last element */
	ref V back() @property
	{
		return buf.ptr[0..count][$-1];	// will use correct bounds-check
	}

	/** ditto */
	ref const(V) back() const @property
	{
		return buf.ptr[0..count][$-1];	// will use correct bounds-check
	}

	int prune(int delegate(ref V val, ref bool remove) dg)
	{
		size_t a=0;
		size_t b;
		int r;
		for(b = 0; b < length; ++b)
		{
			bool remove = false;
			if(0 != (r = dg(this[b], remove)))
				break;

			if(!remove)
			{
				if(b != a)
					this[a] = move(this[b]);
				++a;
			}
		}

		for(; b < length; ++b)
		{
			if(b != a)
				this[a] = move(this[b]);
			++a;
		}

		this.resize(a);

		return r;
	}


	//////////////////////////////////////////////////////////////////////
	/// add, remove
	//////////////////////////////////////////////////////////////////////

	/** add some new element to the back */
	void pushBack(T:V)(T val)
	{
		if(count == buf.length)
		{
			auto newBuf = new V[buf.length ? buf.length * 2 : startSize];
			moveAll(buf[], newBuf[0..buf.length]);
			buf = newBuf;
		}
		buf.ptr[count] = move(val);
		++count;
	}

	/** add multiple new elements to the back */
	void pushBack(Stuff)(Stuff data)
		if(!is(Stuff:V) && isInputRange!Stuff && is(ElementType!Stuff:V))
	{
		static if(hasLength!Stuff)
			reserve(count + data.length);

		foreach(x; data)
			pushBack(x);
	}

	/** convenience function for pushBack */
	ref Array opCatAssign(T:V)(T data)
	{
		pushBack(data);
		return this;
	}

	/** ditto */
	ref Array opCatAssign(Stuff)(Stuff data)
		if(!is(Stuff:V) && isInputRange!Stuff && is(ElementType!Stuff:V))
	{
		pushBack(data);
		return this;
	}

	/** returns removed element */
	V popBack()
	{
		return move(buf[--count]);
	}

	/** sets the size to some value. Either cuts of some values (but does not free memory), or fills new ones with V.init */
	void resize(size_t newsize)
	{
		if(newsize > capacity)
		{
			reserve(newsize);
			buf[count..newsize] = V.init;	// TODO: use moveAll
		}
		count = newsize;
	}


	//////////////////////////////////////////////////////////////////////
	/// comparision
	//////////////////////////////////////////////////////////////////////

	hash_t toHash() const nothrow @trusted @property
	{
		hash_t h = length*17;
		foreach(ref x; buf[0..count])
			h = 19*h+23*typeid(V).getHash(&x);
		return h;
	}

	bool opEquals(const ref Array other) const nothrow
	{
		return this[] == other[];
	}

	int opCmp(const ref Array other) const
	{
		auto a = this[];
		auto b = other[];
		return typeid(typeof(a)).compare(&a, &b);
	}


	//////////////////////////////////////////////////////////////////////
	/// internals
	//////////////////////////////////////////////////////////////////////

	private V[] buf = null;		// .length = capacity
	private size_t count = 0;	// used size
	private enum startSize = 4;	// tuneable. No investigation done.
}


/**
 *  pretty much the thing, STL called vector. never shrinks. value semantic.
 */
struct FlatQueue(V)
{
	//////////////////////////////////////////////////////////////////////
	/// constructors
	//////////////////////////////////////////////////////////////////////

	/** constructor for given length */
	this(size_t size)
	{
		buf = new V[size];
	}

	/** post-blit that does a full copy */
	this(this)
	{
		static import std.stdio	;// TODO: remove this
		if(buf.length != 0)
			std.stdio.writefln("called copy-constructor on FlatQueue!%s of length %s", V.stringof, length);
		buf = buf.dup;
	}


	//////////////////////////////////////////////////////////////////////
	/// metrics
	//////////////////////////////////////////////////////////////////////

	/** check for emptiness */
	bool empty() const nothrow @property @safe
	{
		return a==b;
	}

	/** number of elements */
	size_t length() const nothrow @property @safe
	{
		return b-a;
	}


	//////////////////////////////////////////////////////////////////////
	/// indexing, add, remove
	//////////////////////////////////////////////////////////////////////

	/** first element */
	ref V front() @property
	{
		return buf.ptr[a..b][0];	// will use correct bounds-check
	}

	/** add some new element to the back */
	void push(T:V)(T val)
	{
		assert(b != buf.length);
		buf[b++] = move(val);
	}


	/** returns removed element */
	V pop()
	{
		auto x = move(buf[a++]);
		if(a==b)
			clear();
		return move(x);
	}

	void clear()
	{
		a = b = 0;
	}

	//////////////////////////////////////////////////////////////////////
	/// internals
	//////////////////////////////////////////////////////////////////////

	private V[] buf = null;
	private size_t a = 0, b = 0;	// indices for in/out
}
