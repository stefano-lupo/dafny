/*
	isPrefix
*/
predicate isPrefixPred(pre:string, str:string) {
	|pre| > 0 && (|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string) {
	|pre| <= 0 || (|pre| > |str|) || pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	if (|pre| > |str| || |pre| <= 0) {
		return false;
	}

	return str[..|pre|] == pre;
}






/*
	isSubstring
*/
predicate isSubstringPred(sub:string, str:string) {
	(0 < |sub| <= |str|) && (exists i :: 0 <= i <= |str| - |sub| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string) {
	!(0 < |sub| <= |str|) || (forall i :: 0 <= i <= |str| - |sub| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

// This should probably hold..

//lemma PrefixImpliesSubstringLemma(pre:string, str:string)
//	ensures isPrefixPred(pre, str) ==> isSubstringPred(pre, str)
//	ensures isNotSubstringPred(pre, str) ==> isNotPrefixPred(pre, str)
//{}

lemma PrefixImpliesSubstringLemma(sub:string, str:string) 
	// The existance of an x such that sub is a prefix of str[x..] implies that sub is a substring of x
	ensures (exists x :: 0 <= x <= |str| - |sub| && isPrefixPred(sub, str[x..])) ==> isSubstringPred(sub, str)
	
	// If sub is not a prefix of str[x..] for all x, then sub is not a substring of str
	ensures (forall x :: 0 <= x <= |str| - |sub| ==> isNotPrefixPred(sub, str[x..])) ==> isNotSubstringPred(sub, str)

	// Given that sub is a prefix of str implies sub is a substring of str (DOESNT HOLD!)
	//ensures isPrefixPred(sub, str) ==> isSubstringPred(sub, str)
{}

// This holds for res ==> isSubstr and isNotRes  ==> !res
// Doesn't hold for other way arounds though
method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res ==> isSubstringPred(sub, str)
	ensures isSubstringPred(sub, str) ==> res
	ensures !res ==> isNotSubstringPred(sub, str)
	ensures isNotSubstringPred(sub, str) ==> !res
{

	// Short circuit exit
	if !(0 < |sub| <= |str|) {
		return false;
	}

	var i := 0;
  res := false;

	while (i <= |str| - |sub| && !res)
	decreases (|str| - |sub| - i) + (if res then 0 else 1)
  invariant 0 <= i <= (|str| - |sub|) + 1
  invariant res ==> isSubstringPred(sub, str)
  invariant forall x :: 0 <= x < i ==> !isPrefixPred(sub, str[x..])
	{
		var tail := str[i..];
		res := isPrefix(sub, tail);
    if (!res) {
      i := i +1;
    }
	}
}







/*
	K Substring

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string) {
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string) {
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  ==>  haveCommonKSubstringPred(k,str1,str2)
	ensures haveCommonKSubstringPred(k,str1,str2) ==> found
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
// If either strings are smaller than k, they have no common substring of size k
	if (|str1| < k || |str2| < k) {
		assert haveNotCommonKSubstringPred(k, str1, str2);
		return false;
	}

	// Create each substring of size k from str1
	var startIndex := 0;
	while (startIndex <= |str1| - k) 
	
	{
		var endIndex := startIndex + k;

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
*/