method Abs(x: int) returns (y: int) {
  if (x < 0) {
    return -x;
  }

  return x;
}

// assignment operator is := in Dafny
// Values can be returned by just setting the named variables
// return on its own will return the current assignment of these variables
// Or you can return values / variables as normal (eg return -1, return x)
method MultipleReturns(x: int, y: int) returns (more: int, less: int) {
   more := x + y;
   less := x - y;
}

// Sequences
predicate sorted(mySeq: seq<int>) {
  forall i, j :: 0 <= i < j < |mySeq| ==> mySeq[i] <= mySeq[j]
}

// Using recursion: sorted iff first element is smaller than the rest AND rest are sorted
predicate sorted2(mySeq: seq<int>) {
  0 < |mySeq| ==> ((forall i :: 0 < i < |mySeq| ==> mySeq[0] <= mySeq[i]) && sorted2(mySeq[1..]))
}


// Note: Sequences are immutable
method SequenceNotes(mySeq: seq<int>) {
  var otherSeq := [1, 2, 3];
  var singletonBoolean := [true];
  // var empty :== []; // There is a way to generate empties

  var s := [1, 2, 3, 4, 5];
  
  assert s[|s| - 1] == 5;               								// Get last element
  assert s[|s| - 1 .. |s|] == [5];											// Get last element as singleton sequence
	assert s[1..] == [2, 3, 4, 5];												// Slice notation
	assert s[ .. |s|-1] == [1, 2, 3, 4];									// More slice notation
	assert s == s[0..] == s[..|s|] == s[0..|s|] == s[..];	// All slice types

	assert [1, 2, 3] == [1] + [2, 3];											// Sequence concatenation
	assert s == s + [];																		// Empty sequence
	assert forall i :: 0 <= i <= |s| ==> 
		s == s[..i] + s[i..];																// Less than equal to seems odd here..
	
	assert 5 in s;																				// Inclusion
	assert 0 !in s;																				// Exclusion

	var p := [2, 3, 1, 0];
	assert forall i :: i in p ==> 0 <= i < |s|;						// For each - assert that everything in p is an index into s

	// s[0 := 99];																				// Update array indices in immutable way - see func below

	assert forall k :: 0 <= k < |s| ==> -1 != s[k]; 			// Assert -1 is not in s
	assert -1 !in s;																			// Shortcut
	assert -1 !in s[1..];																	// Not in last n - 1 elements
}

function updateSequenceByIndex(s: seq<int>, i: int, newVal: int): seq<int>
	requires 0 <= i < |s|																								// Precondition
	ensures updateSequenceByIndex(s, i, newVal) == s[i := newVal]				// Postconditon
{
	s[..i] + [newVal] + s[i+1..]
}