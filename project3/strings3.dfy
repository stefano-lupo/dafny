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
	//(exists i :: 0 <= i < |str| &&  isPrefixPred(sub, str[i..]))
	|sub| > 0 && |str| > 0 && |str| >= |sub| && (exists i :: 0 <= i < |str| - |sub| && isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string) {
	//(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
	|sub| <= 0 || |str| <= 0 || (forall i :: 0 <= i <= |str| - |sub| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)

{}

// This not holding seems like a problem..
lemma isPrefix_isSubstring(sub: string, str: string)
	ensures isPrefixPred(sub, str) ==> isSubstringPred(sub, str)
	//ensures isNotPrefixPred(sub, str) ==> isNotSubstringPred(sub, str)
{}


predicate containsSubstringAtIndices(sub:string, str:string, start:nat, end:nat) {
	0 <= start < end < |str| && end - start == |sub| && 0 < |sub| <= |str| && str[start..end] == sub
}

lemma test(sub: string, str:string, start:nat, end:nat)
ensures containsSubstringAtIndices(sub, str, start, end) <== isSubstringPred(sub, str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res ==> isSubstringPred(sub, str)
	//ensures isSubstringPred(sub, str) ==> res
	//ensures !res ==> isNotSubstringPred(sub, str)
	ensures isNotSubstringPred(sub, str) ==> !res
{

	// Short circuit exit
	if !(0 < |sub| <= |str|) {
		return false;
	}

	var i := 0;
	res := false;

	while (i <= |sub| - |str| && !res)

	// |str| always >= sub, so i will always be less than or equal to length string
	invariant 0 <= i <= (|str| - |sub|) < |str|

	// If we don't short circuit the loop, then result should be false
	invariant (i > |str| - |sub|) ==> !res

	// If sub is not a prefix of str[i..], then str[..i+|sub|] is not a string
	//invariant isNotPrefixPred(sub, str[i..]) ==> isNotSubstringPred(sub, headString)

	// If we don't short circuit the loop, then sub is not a substring
	invariant (i > |str| - |sub|) ==> 
		(forall x :: 0 <= x < |str| ==> isPrefixPred(sub, str[x..]) == isNotSubstringPred(sub, str))

	invariant isPrefixPred(sub, str[i..]) ==> (res == true)

	//invariant (i > |str| - |sub|) ==> forall x :: 0 <= x <= |str| - |sub| ==> isNotSubstringPred(sub, str[x..])

	// If the tail from a given index is not a prefix,
	// Then the substring from [0..(i+|sub|)] is not a substring
	// This would let dafny know that each iteration we are increasing how much of the start of the string
	// is not a substring
	//invariant movingEndIndex <= |str|
	//invariant isNotPrefixPred(sub, str[i..]) ==> isNotSubstringPred(sub, str[..movingEndIndex])
	//invariant isPrefixPred(sub, str[i..]) ==> isSubstringPred(sub, str[..movingEndIndex])


	//invariant (i > |str| - |sub|) ==> (forall x :: 0 <= x <= |str| - |sub| ==> isNotPrefixPred(sub, str[x..]))
	//invariant (i > |str| - |sub|) ==> isNotSubstringPred(sub, str)
	{
		var tail := str[i..];
		var isAPrefix := isPrefix(sub, tail);
		if (isAPrefix) {
			assert isPrefixPred(sub, tail);
			assert isSubstringPred(sub, str);
			res := true;
			break;
			//return true;
		} else {
			// Proves that the truncated tail is not a prefix / substring
			assert isNotPrefixPred(sub, tail);
			assert isNotSubstringPred(sub, tail[..|sub|]);
			
			// Needs to be able to prove that str truncated to (i + |sub|) is also not a substring
			lengthOfHeadStringChecked := i + |sub|;
			assert lengthOfHeadStringChecked <= |str|;
			headString := str[..lengthOfHeadStringChecked];
			//assert isNotSubstringPred(sub, str[..lengthOfHeadStringChecked]);
			//movingEndIndex := i + |sub|;
			//assert isNotSubstringPred(sub, str[..movingEndIndex]);
			if (i < |str| - |sub|) {
				i := i + 1;
			} else {
				break;
			}
		}
	}

	if (!res) {
		// Loop has run to compleition
		assert |str| - |sub| ==  i;
		//assert forall x :: 0 <= x <= |str| - |sub| ==> isNotPrefixPred(sub, str[x..]);
		assert isNotSubstringPred(sub, str[i..]);
	} else {
		assert isSubstringPred(sub, str);
		assert exists x :: 0 <= x <= |str| - |sub| && isPrefixPred(sub, str[x..]);
	}

	return res;
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


method main() {
	var x := isPrefix("", "");
}