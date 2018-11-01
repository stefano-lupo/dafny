/* 
	CS4504 - Formal Verification
	Dr Vasileios Koutavas
	Group Assignment 2 - Predicates about string search
	Stefano Lupo:		14334933 - 4 hours 
		It really should have only taken 1 hour 
		Most of the time was spent trying to figure out why certain approaches would fail in Dafny
	Rowan Sutton:		13330793 - 3 Hours
		About 2 of the 3 hours were spent debugging the substring and k substring premises
*/

predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	|pre| > |str| || !(pre == str[..|pre|])  // DeMorgan
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}



predicate isSubstringPred(sub:string, str:string) {
	|sub| <= |str| && |sub| > 0 &&
	exists x :: 0 <= x <= (|str| - |sub|) && isPrefixPred(sub, str[x..])
}

predicate isNotSubstringPred(sub:string, str:string) {
	|sub| > |str| || |sub| <= 0 || 
	forall x :: 0 <= x <= (|str| - |sub|) ==> isNotPrefixPred(sub, str[x..])
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}



predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string) {
	|str1| >= k && |str2| >= k && 
	exists x :: 0 <= x <= (|str1| - k) && isSubstringPred(str1[x..][..k], str2) 
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string) {
	|str1| < k || |str2| < k ||
	forall x :: 0 <= x <= (|str1| - k) ==> isNotSubstringPred(str1[x..][..k], str2)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}
