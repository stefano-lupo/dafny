predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	// TODO: your formula should not contain &&
	|pre| > |str| || !(forall x :: 0 <= x < |pre| ==> pre[x] == str[x])

	// Not sure why these don't work..
	//|pre| > |str| || (exists x :: 0 <= x < |pre| ==> pre[x] != str[x])
}

/*
lemma PrefixNegationLemmaExpanded(pre:string, str:string) 
ensures isPrefixPred(pre, str) ==> !(isNotPrefixPred(pre, str))
ensures !(isNotPrefixPred(pre, str)) ==> isPrefixPred(pre, str)
ensures !(isPrefixPred(pre, str)) ==> isNotPrefixPred(pre, str)
ensures isNotPrefixPred(pre, str) ==> !(isPrefixPred(pre, str))
{}
*/

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)	// is a prefix applies both ways
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str) // is not a prefix applies both ways
{}












// Excplicit char by char checking in the substrings
predicate isSubstringPred(sub:string, str:string)
{
	|str| >= |sub| && exists k :: (0 <= k <= (|str| - |sub|) 
		==> (forall x :: k <= x < k+|sub| ==> str[x] == sub[x-k]))

}

// Using prefix predicate
predicate isSubstringPred2(sub:string, str:string) {
	|str| >= |sub| && exists k :: (0 <= k <= (|str| - |sub|) 
		==> isPrefixPred(sub, str[k..]))
}

// Using sublists
predicate isSubstringPred3(sub:string, str:string) {
	|str| >= |sub| && exists k :: (0 <= k <= (|str| - |sub|) 
		==> str[k..][..|sub|] == sub)
}

lemma substringPredsAggreee(sub:string, str:string) 
	//ensures isSubstringPred(sub, str) <==> isSubstringPred2(sub, str) 
	//ensures isSubstringPred2(sub, str) <==> isSubstringPred3(sub, str) 
	//ensures isSubstringPred(sub, str) ==> isSubstringPred3(sub, str)
	//ensures isSubstringPred3(sub, str) ==> isSubstringPred(sub, str) 
{}


predicate isNotSubstringPred(sub:string, str:string)
{
	|sub| > |str| && !isSubstringPred(sub, str)
}

predicate isNotSubstringPred3(sub:string, str:string)
{
	|str| < |sub| || !(exists k :: (0 <= k <= (|str| - |sub|) 
		==> str[k..][..|sub|] == sub))
}


lemma SubstringNegationLemmaExpanded(sub:string, str:string) 
	ensures isSubstringPred(sub,str) ==> !isNotSubstringPred(sub,str)		// is substring, but not not a substring
	ensures !isNotSubstringPred(sub,str) ==> isSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) ==>  isNotSubstringPred(sub,str)
	ensures isNotSubstringPred(sub,str) ==> !isSubstringPred(sub,str)
{}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

lemma SubstringNegationLemmaExpanded3(sub:string, str:string) 
	ensures isSubstringPred3(sub,str) ==> !isNotSubstringPred3(sub,str)		// is substring, but not not a substring
	ensures !isNotSubstringPred3(sub,str) ==> isSubstringPred3(sub,str)
	ensures !isSubstringPred3(sub,str) ==>  isNotSubstringPred3(sub,str)
	ensures isNotSubstringPred3(sub,str) ==> !isSubstringPred3(sub,str)
{}
















/*
predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
  //TODO
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	//TODO: your FOL formula should start with a forall
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}
*/