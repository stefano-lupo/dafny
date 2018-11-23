predicate isMax(s:seq<int>, lo:int) {
	0 <= lo < |s| && forall x :: 0 <= x < |s| ==> s[lo] >= s[x]
}


method findMax(s:seq<int>) returns (lo:int) 
requires 0 < |s|
ensures isMax(s, lo)
{
	lo := 0;
	var hi := |s|-1;

	// Just to make dafny accept the bounds
	while (lo < hi && 0 <= lo <= hi < |s|)
	invariant 0 <= lo <= hi < |s| && |s| > 0 &&

	// The max will always lie between the lo and hi indicies
	hi >= lo && exists x :: (lo <= x <= hi && isMax(s, x))
	{
		if (s[lo] <= s[hi]) {
			lo := lo + 1;
		} else {
			hi := hi - 1;
		}
	}
}


