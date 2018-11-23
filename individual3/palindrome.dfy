
predicate isPal(s:string) {
	forall x :: 0 <= x < |s| ==> (exists y :: y == (|s| - x - 1) && s[x] == s[y])
}

method palindrome(s:string) returns (result:int) 
requires |s| >= 0
ensures (result == 1) <==> isPal(s)
{
  result := 1;
	var i := 0;
	var j := (|s| - 1);

	// Extra loop conditions so dafny knows indices are valid
	while (i < j && result == 1 && (0 <= i < |s|) && (0 <= j < |s|))
	invariant 0 <= i < |s| && 0 <= j < |s| &&
	(i >= j ==> isPal(s)) && 
	((result == 0) ==> !isPal(s))
	{
		if (s[i] != s[j]) {
			result := 0;
		} else {
			// No op
		}

		i := i + 1;
		j := j - 1;
	}
}
