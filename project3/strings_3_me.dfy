/*
	isPrefix
*/
predicate isPrefixPred(pre:string, str:string) {
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string) {
	(|pre| > |str|) || pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	if (|pre| > |str|) {
		return false;
	}

	return str[..|pre|] == pre;
}






/*
	isSubstring
*/
predicate isSubstringPred(sub:string, str:string) {
  exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..])
}

predicate isNotSubstringPred(sub:string, str:string) {
	forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..])
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


method isSubstring(sub: string, str: string) returns (res:bool)
  // Dont even require invariants
	ensures  res ==> isSubstringPred(sub, str)
	ensures isNotSubstringPred(sub, str) ==> !res

  // Require invariants
  ensures isSubstringPred(sub, str) ==> res
	ensures !res ==> isNotSubstringPred(sub, str)
{

	// Short circuit exit
	if !(|sub| <= |str|) {
		return false;
	}

	var i := 0;
  res := false;

	while (i <= |str| - |sub|)
	decreases (|str| - |sub| - i)
  invariant res ==> isSubstringPred(sub, str)
  invariant i <= |str|
  invariant forall x :: 0 <= x < i ==> isNotPrefixPred(sub, str[x..])
	{
		var tail := str[i..];
		var isAPrefix := isPrefix(sub, tail);
		if (isAPrefix) {
			assert isPrefixPred(sub, tail);
			assert isSubstringPred(sub, str);
			return true;
		} else {
			assert isNotPrefixPred(sub, tail);
			assert isNotSubstringPred(sub, tail[..|sub|]);
      i := i + 1;
		}
	}
}







/*
	K Substring

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string) {
	exists i1, j1 :: 0 <= i1 <= |str1|- k && (j1 == i1 + k) && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string) {
	forall i1, j1 :: 0 <= i1 <= |str1|- k && (j1 == i1 + k) ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
   // Trivial
  ensures found  ==>  haveCommonKSubstringPred(k,str1,str2)
  ensures haveNotCommonKSubstringPred(k,str1,str2) ==> !found

  // Not Trivial
  ensures haveCommonKSubstringPred(k,str1,str2) ==> found
	ensures !found ==> haveNotCommonKSubstringPred(k,str1,str2)
{
  // If either strings are smaller than k, they have no common substring of size k
	if (|str1| < k || |str2| < k) {
		assert haveNotCommonKSubstringPred(k, str1, str2);
		return false;
	}

  var s1 := "";
  var s2 := "";
  assert s1 == s2;
  assert s1[0..0] == s2[0..];


  if (k == 0) {
    //assert isPrefixPred(str1[0..0], str2[0..]);
    //return true;
  }

	// Create each substring of size k from str1
	var startIndex := 0;
  var endIndex := startIndex + k;
  found := false;
	while (startIndex <= |str1| - k) 
  
  //invariant 0 <= startIndex <= endIndex <= |str1|
  //invariant found ==> haveCommonKSubstringPred(k, str1, str2)
  //invariant isSubstringPred(str1[startIndex..endIndex], str2) ==> haveCommonKSubstringPred(k, str1, str2)
  //invariant haveCommonKSubstringPred(k, str1[startIndex..endIndex], str2) ==> found
	
	{
		endIndex := startIndex + k;

		// Ensure largest index is the number of elements in sequence
		// It can reach the number of elements in the sequence as slice is closed at end of interval 
		assert endIndex <= |str1|;

		// Get a substring of length k from str1							
		var substr := str1[startIndex..endIndex];
		assert |substr| == k;

		var isSubstr := isSubstring(substr, str2);
		if (isSubstr) {
			return true;
		}

		startIndex := startIndex + 1;
	}

	return false;
}
