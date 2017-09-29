module sat.activityheap;

import sat.sat;
private import jive.array;

/** heap of variables with quick access to the most 'active' on */
struct ActivityHeap
{
	@disable this(this);

	this(Sat sat)
	{
		this.sat = sat;
		location.resize(sat.varCount, -1);
	}

	/** returns: true if set is empty */
	bool empty() const @property @safe
	{
		return arr.empty;
	}

	/** returns: number of elements in the set */
	size_t length() const @property @safe
	{
		return arr.length;
	}

	/** check if a var is currently present in th heap */
	bool opIn_r(int var)
	{
		return location[var] != -1;
	}

	/** Removes most active variable from heap and returns it. */
	int pop()
	{
		assert(!empty);
		int r = arr.front;
		location[r] = -1;
		arr.front = arr.popBack;
		if(!empty)
			percolateDown(0);
		return r;
	}

	/** Add a variable to the queue. If it is already in, update it. */
	void push(int var)
	{
		if(var in this)
		{
			percolateUp(location[var]);
			percolateDown(location[var]);
		}
		else
		{
			arr.pushBack(var);
			percolateUp(cast(int)length-1);
		}
	}

	/** Notifiy the heap that the activity of var has changed. Does nothing if not currently in the heap. */
	void update(int var)
	{
		if(var !in this)
			return;
		percolateUp(location[var]);
		percolateDown(location[var]);
	}

	//////////////////////////////////////////////////////////////////////
	// internals
	//////////////////////////////////////////////////////////////////////

	private Sat sat;
	private Array!int arr;
	private Array!int location; // -1 for vars that are not in the heap currently

	private int parent(int i) { return (i-1)/2; }
	private int left(int i) { return 2*i+1; }
	private int right(int i) { return 2*i+2; }

	private bool pred(int x, int y)
	{
		return sat.varData[x].activity > sat.varData[y].activity;
	}

	private int smallerChild(int i)
	{
		if(right(i) < length && pred(arr[right(i)], arr[left(i)]))
			return right(i);
		else
			return left(i);
	}

	private void percolateUp(int i)
	{
		auto x = arr[i];

		for(int p = parent(i); i != 0 && pred(x, arr[p]); i = p, p = parent(i))
		{
			arr[i] = arr[p];
			location[arr[i]] = i;
		}

		arr[i] = x;
		location[x] = i;
	}

	private void percolateDown(int i)
	{
		auto x = arr[i];

		for(int c = smallerChild(i); c < length && pred(arr[c], x); i = c, c = smallerChild(i))
		{
			arr[i] = arr[c];
			location[arr[i]] = i;
		}

		arr[i] = x;
		location[x] = i;
	}
}
