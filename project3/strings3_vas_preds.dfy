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
	//ensures isSubstringPred(sub, str) ==> res
	//ensures !res ==> isNotSubstringPred(sub, str)
	ensures isNotSubstringPred(sub, str) ==> !res
{

	// Short circuit exit
	if !(0 < |sub| <= |str|) {
		return false;
	}

	res := isPrefix(sub, str);
	if (res) {
		assert(isPrefixPred(sub, str));
		assert 
		assert isPrefixPred(sub, str) ==> (exists x :: 0 <= x <= |str| - |sub| && isPrefixPred(sub, str[x..]));
		return true;
	}


	var i := 0;
	var lengthOfHeadStringChecked := i + |sub|;
	var headString := str[..lengthOfHeadStringChecked];
	
	assert |str| - |sub| >= 0;
	assert lengthOfHeadStringChecked <= |str|;

	while (true)

	decreases (|str| - |sub|) - i

	// |str| always >= sub, so i will always be less than or equal to length string
	invariant 0 <= i <= (|str| - |sub|) < |str|

	// If we don't short circuit the loop, then result should be false
	invariant (i > |str| - |sub|) ==> !res

	// The max this will ever be is |str| 
	invariant lengthOfHeadStringChecked <= |str|
	invariant |headString| <= |str|;
	invariant headString == str[..lengthOfHeadStringChecked]

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