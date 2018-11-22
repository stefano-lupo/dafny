predicate unique(s:seq) {
	forall x :: 0 <= x < |s| ==> ! exists y :: x < y < |s| && s[x] == s[y]
}

predicate unique_explicit(s:seq) {
	forall x :: 0 <= x < |s| ==> ! exists y :: 0 <= y < |s| && x != y && s[x] == s[y]
}


// Sanity check: Dafny should be able to automatically prove the following lemma
lemma unique_lemma(s:seq)
	ensures  unique(s) <==> unique_explicit(s)
{}

predicate palindrome_predicate(s:string) {
	forall x :: 0 <= x < |s| ==> (exists y :: 0 <= y < |s| && y == (|s| - x - 1) && s[x] == s[y])
}

method palindrome(s:string) returns (result_bool:bool) 
requires |s| >= 0
//ensures result_bool == palindrome_predicate(s)
{
  var result:= 1;
	var i := 0;
	var j := (|s| - 1);

	while (i < j && result == 1 && (0 <= i < |s|) && (0 <= j < |s|))
	invariant i + j + 1 == |s|
	{
		if (s[i] != s[j]) {
			result := 0;
		} else {
			// No op
		}

		i := i + 1;
		j := j - 1;
		print("i = ");
		print(i);
		print("\n");
		print("j = ");
		print(j);
		print("\n");
	}

 	result_bool := false;
	if (result == 1) {
		result_bool := true;
	}
}

method Main() {
	print ("Hello world\n");
	var isPalindrome := palindrome("aa");
	print(isPalindrome);
}