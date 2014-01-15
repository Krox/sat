module jive.flatset;

import jive.array;
private import std.algorithm : sort;

/** set structure implemented as sorted array.
 *  NOTE: elements may not change (w.r.t. their relative order)
 *  TODO: use 'move' to avoid postblits for complex types V
 */
struct FlatSet(V)
{
	Array!V vals;
	alias vals this;	// NOTE: not all operations on the Array are actually fine, but I dont want to write any boring wrappers

	//////////////////////////////////////////////////////////////////////
	/// constructors
	//////////////////////////////////////////////////////////////////////

	this(V[] val)
	{
		vals = Array!V(val);

		if(empty)
			return;

		// NOTE: dont use "this[].sort", because of dmd bug (d.puremagic.com/issues/show_bug.cgi?id=11932)
		sort(vals[]);

		size_t j = 1;
		for(size_t i = 1; i < length; ++i)
			if(vals[i] != vals[j-1])
				swap(vals[i], vals[j++]);

		vals.resize(j);
	}

	//////////////////////////////////////////////////////////////////////
	/// set operations
	//////////////////////////////////////////////////////////////////////

	/* TODO: merge, disect, etc */

	//////////////////////////////////////////////////////////////////////
	/// find
	//////////////////////////////////////////////////////////////////////

	/** find element with given value. if not found, returns position where it should be inserted*/
	size_t findPos(const /*ref*/ V v) const
	{
		size_t a=0, b=length;

		while (a != b)
		{
			size_t m = (a+b)/2;

			if (this[m] < v)
				a = m+1;
			else
				b = m;
		}

		return a;
	}

	/** find element with given value. if not found, returns length */
	size_t find(const /*ref*/ V v) const
	{
		auto i = findPos(v);
		if(i < length && this[i] == v)
			return i;
		else
			return length;
	}

	//////////////////////////////////////////////////////////////////////
	/// add, remove
	//////////////////////////////////////////////////////////////////////

	bool add(V v)
	{
		auto p = findPos(v);
		if(p < length && this[p] == v)
			return false;
		insert(p, v);
		return true;
	}

	/** remove (at most) one element with value v */
	bool remove(const /*ref*/ V v)
	{
		size_t i = find(v);
		if(i == length)
			return false;
		vals.remove(i);
		return true;
	}
}
