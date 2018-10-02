/* 
	Stefano Lupo:		14334933 - 30 mins on Dafny setup, 1 hour on Dafny tutorial, 1 hour on assignment
	Rowan Sutton:		99999999 - 	
*/

// Returns true iff pre is a prefix of str
method isPrefix(pre: string, str: string) returns (res: bool) 
//	requires |pre| > 0 && |str| > 0
{
	if (|pre| > |str|) {
		return false;
	}

	var charsOfInterest := str[..|pre|];
	assert |charsOfInterest| == |pre|;

	return str[..|pre|] == pre;
}

// Returns true if sub is a substring of str
method isSubstring(sub: string, str: string) returns (res: bool) 
//	requires |sub| > 0 && |str| > 0
{
	var isAPrefix := isPrefix(sub,  str);

	if (isAPrefix) {
		return true;
	}

	if (|str| <= 1) {
		return false;
	}
	
	var next := str[1..];
	res :=  isSubstring(sub, next);
}

// Returns true iff str1 and str2 have a common substring of length k
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool) 
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

// Returns the length of the largest common substring of str1 and str2 (0 if no common substring)
method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat) {
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