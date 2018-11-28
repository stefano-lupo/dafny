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
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string) {
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)

{}
lemma PrefixImpliesSubstringLemma(sub:string, str:string) 
	// The existance of an x such that sub is a prefix of str[x..] implies that sub is a substring of x
	ensures (exists x :: 0 <= x <= |str| - |sub| && isPrefixPred(sub, str[x..])) ==> isSubstringPred(sub, str)
	
	// If sub is not a prefix of str[x..] for all x, then sub is not a substring of str
	ensures (forall x :: 0 <= x <= |str| - |sub| ==> isNotPrefixPred(sub, str[x..])) ==> isNotSubstringPred(sub, str)

	// Given that sub is a prefix of str implies sub is a substring of str (DOESNT HOLD!)
{}
	//ensures isPrefixPred(sub, str) ==> isSubstringPred(sub, str)

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	var isAPrefix := isPrefix(sub,  str);

	if (isAPrefix) {
		return true;
	}

	// Ensure we can create a subtring ignoring first char
	if (|str| <= 1) {
		return false;
	}
	
	// Drop first character of string
	var nextStringToCheck := str[1..];

	// Recurse using the remaining chars 
	res :=  isSubstring(sub, nextStringToCheck);
}






/*
	K Substring
*/
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
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
// If either strings are smaller than k, they have no common substring of size k
	if (|str1| < k || |str2| < k) {
		return false;
	}

	// Find the smaller and larger of the two strings
	var smaller := str1;
	var larger := str2;
	if (|str2| < |str1|) {
		smaller := str2;
		larger := str1;
	}

	// Create each substring of size k from the smaller string
	// Use smaller string in loop to reduce number of iterations
	var i := 0;
	while (i <= |smaller| - k) {

		// Ensure largest index is the number of elements in sequence
		// It can reach the number of elements in the sequence as slice is closed at end of interval 
		assert (i + k) <= |smaller|;

		// Get a substring of length k from smaller							
		var substr := smaller[i..i+k];
		assert |substr| == k;

		var isSubstr := isSubstring(substr, larger);
		if (isSubstr) {
			return true;
		}

		i := i + 1;
	}

	return false;
}




/*
	maxCommonSubstringLength
*/
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{


	// Calculate the max substring length	
	var maxSubstringLength := |str1|;
	if (|str2| < |str1|) {
		maxSubstringLength := |str2|;
	}

	len := maxSubstringLength;
	while (len > 0) {
		var hasCommonSubstrOfLen := haveCommonKSubstring(len, str1, str2);
		if (hasCommonSubstrOfLen) {
			return len;
		}
		len := len - 1;
	}

	return len;

}