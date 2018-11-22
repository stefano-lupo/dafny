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
/*
predicate isSubstringPred(sub:string, str:string)
{
	|str| >= |sub| && 
	exists k :: (0 <= k <= (|str| - |sub|) ==> 
		(forall x :: k <= x < k+|sub| ==> str[x] == sub[x-k]))

}
*/


// Using prefix predicate
predicate isSubstringPredUsingPrefix(sub:string, str:string) {
	|str| >= |sub| && |sub| != 0 && 
	exists k :: (0 <= k <= (|str| - |sub|) 
		==> isPrefixPred(sub, str[k..]))
}


// Using sublists
predicate isSubstringPred(sub:string, str:string) {
	|str| >= |sub| && |sub| != 0 && |str| != 0 && 
	exists k :: (0 <= k <= (|str| - |sub|) 
		==> str[k..][..|sub|] == sub)
}

predicate isSubstringPredRowan(sub:string, str:string) {
	(|sub| <= |str|) && (|sub| != 0) && (|str| != 0) && 
	exists x :: (0 <= x <= (|str|-|sub|) 
		==> exists y :: (y == (|sub| + x) ==> str[x..y]==sub))
}


lemma substringPredsAggreee(sub:string, str:string) 
	//ensures isSubstringPred(sub, str) <==> isSubstringPredRowan(sub, str) 
	//ensures isSubstringPred(sub, str) ==> isSubstringPredUsingPrefix(sub, str) 
	//ensures isSubstringPredRowan(sub, str) <==> isSubstringPredUsingPrefix(sub, str)
	//ensures isSubstringPredUsingPrefix(sub, str) ==> isSubstringPred(sub, str) 
{}



// Using sublists
predicate isNotSubstringPred(sub:string, str:string) {
	|str| < |sub| || |sub| == 0 || |str| == 0 || 
	forall k :: (0 <= k <= (|str| - |sub|) 
		==> str[k..][..|sub|] != sub)
}

/*
predicate isNotSubstringPred3(sub:string, str:string)
{
	|str| < |sub| || !(exists k :: (0 <= k <= (|str| - |sub|) 
		==> str[k..][..|sub|] == sub))
}
*/


/*
predicate test(str:string, sub:string) {
	|str| >= |sub| &&
	forall x :: 0 <= x <= (|str| - |sub|) ==>
		forall y :: 0 <= y <= |sub| ==>
			forall z :: z == x + y ==> 
				str[x..z] == str[x..][..y]
}
*/

lemma SubstringNegationLemmaExpanded(sub:string, str:string) 
	ensures isSubstringPred(sub,str) ==> !isNotSubstringPred(sub,str)		// is substring, but not not a substring
	//ensures !isNotSubstringPred(sub,str) ==> isSubstringPred(sub,str)
	//ensures !isSubstringPred(sub,str) ==>  isNotSubstringPred(sub,str)
	//ensures isNotSubstringPred(sub,str) ==> !isSubstringPred(sub,str)
{}

// Sanity check: Dafny should be able to automatically prove the following lemma

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
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