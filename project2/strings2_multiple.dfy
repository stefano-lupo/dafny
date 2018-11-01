predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	!(|pre| <= |str|) || !(pre == str[..|pre|])  // DeMorgan
	// TODO: your formula should not contain &&
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}










/******************************************
	Rowans current method
*******************************************/
predicate isSubstringPredRowan(sub:string, str:string)
{
  (|sub| <= |str|) && (|sub| != 0) && (|str| != 0) && exists x :: (0 <= x <= (|str|-|sub|) ==> exists y :: (y == (|sub| + x) ==> str[x..y]==sub)) 
  // Exists and x for each "position" of the substring
  // Exists y because str[x..x+|sub|] won't work with Dafny
}

predicate isNotSubstringPredRowan(sub:string, str:string)
{
	!(|sub| <= |str|) || (|sub| == 0) || (|str| == 0)  || forall x :: !(0 <= x <= (|str|-|sub|) ==> exists y :: (y == (|sub| + x) ==> str[x..y]==sub))
	//TODO: your FOL formula should start with a forall
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemmaRowan(sub:string, str:string)
	ensures  isSubstringPredRowan(sub,str) <==> !isNotSubstringPredRowan(sub,str)
	ensures !isSubstringPredRowan(sub,str) <==>  isNotSubstringPredRowan(sub,str)
{}





/**********************************************
	Rowans current method with slight adjustments
***********************************************/
predicate isSubstringPredRowanAdjusted(sub:string, str:string)
{
  |sub| <= |str| && |sub| > 0 &&
	exists x :: 0 <= x <= (|str|-|sub|) &&
		(exists y :: (y == (|sub| + x) && str[x..y] == sub))
}

predicate isNotSubstringPredRowanAdjusted(sub:string, str:string)
{
	|sub| > |str| || |sub| <= 0 || 
	forall x :: 0 <= x <= (|str|-|sub|) ==> !(exists y :: y == (|sub| + x) && str[x..y]==sub)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemmaRowanAdjusted(pre:string, str:string)
	ensures  isSubstringPredRowanAdjusted(pre,str) <==> !isNotSubstringPredRowanAdjusted(pre,str)
	ensures !isSubstringPredRowanAdjusted(pre,str) <==>  isNotSubstringPredRowanAdjusted(pre,str)
{}





/*****************************************
	Stefano's way using prefix predicate
******************************************/

predicate isSubstringPredUsingPrefix(sub:string, str:string) {
	|sub| <= |str| && |sub| > 0 &&
	exists x :: 0 <= x <= (|str| - |sub|) && isPrefixPred(sub, str[x..])
}

predicate isNotSubstringPredUsingPrefix(sub:string, str:string) {
	|sub| > |str| || |sub| <= 0 || 
	forall x :: 0 <= x <= (|str| - |sub|) ==> isNotPrefixPred(sub, str[x..])
}

lemma SubstringPrefixNegationLemma(sub:string, str:string)
	ensures  isSubstringPredUsingPrefix(sub,str) <==> !isNotSubstringPredUsingPrefix(sub,str)
	ensures !isSubstringPredUsingPrefix(sub,str) <==>  isNotSubstringPredUsingPrefix(sub,str)
{}


/*****************************************
	Stefano's way using chained subsequencing
******************************************/

predicate isSubstringPredSubseqChain(sub:string, str:string) {
	|sub| <= |str| && |sub| > 0 &&
	exists x :: 0 <= x <= (|str| - |sub|) && str[x..][..|sub|] == sub
}

predicate isNotSubstringPredSubseqChain(sub:string, str:string) {
	|sub| > |str| || |sub| <= 0 || 
	forall x :: 0 <= x <= (|str| - |sub|) ==> !(str[x..][..|sub|] == sub)
}

lemma SubstringSeqChainNegationLemma(sub:string, str:string)
	ensures  isSubstringPredSubseqChain(sub,str) <==> !isNotSubstringPredSubseqChain(sub,str)
	ensures !isSubstringPredSubseqChain(sub,str) <==>  isNotSubstringPredSubseqChain(sub,str)
{}


/*****************************************
	Rowans adjusted predicates 
	Stefano's prefix predicates agree
******************************************/
lemma testEquivalenceOfSubstringPredicates(sub:string, str:string) 
	// Rowan adjusted and Stefano's Prefix
	//ensures isSubstringPredRowanAdjusted(sub, str) ==> isSubstringPredUsingPrefix(sub, str)
	//ensures isSubstringPredRowanAdjusted(sub, str) <== isSubstringPredUsingPrefix(sub, str)
	//ensures isNotSubstringPredRowanAdjusted(sub, str) ==> isNotSubstringPredUsingPrefix(sub, str)
	//ensures isNotSubstringPredRowanAdjusted(sub, str) <== isNotSubstringPredUsingPrefix(sub, str)

	// Stefanos Prefix and Stefanos Subsequence chain
	ensures isSubstringPredSubseqChain(sub, str) <==> isSubstringPredUsingPrefix(sub, str)
	ensures isNotSubstringPredSubseqChain(sub, str) <==> isNotSubstringPredUsingPrefix(sub, str)
{}





/********************************************************
	Rowans Method of K Substring
********************************************************/

predicate haveCommonKSubstringPredRowan(k:nat, str1:string, str2:string)
{
	(|str1| != 0) && (|str2| != 0) && exists x :: (0 <= x < |str1| ==> exists y :: (x < y <= |str1| ==> (isSubstringPredRowan(str1[x..y], str2)  && |str1[x..y]| == k)))
}

predicate haveNotCommonKSubstringPredRowan(k:nat, str1:string, str2:string)
{
	(|str1| == 0) || (|str2| == 0) || forall x :: !(0 <= x < |str1| ==> exists y :: (x < y <= |str1| ==> (isSubstringPredRowan(str1[x..y], str2)  && |str1[x..y]| == k)))
	//TODO: your FOL formula should start with a forall
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemmaRowan(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPredRowan(k,str1,str2) <==> !haveNotCommonKSubstringPredRowan(k,str1,str2)
	ensures !haveCommonKSubstringPredRowan(k,str1,str2) <==> haveNotCommonKSubstringPredRowan(k,str1,str2)
{}

/********************************************************
	Adjusted Rowans Method of K Substring
********************************************************/
/*
predicate haveCommonKSubstringPredAdjusted(k:nat, str1:string, str2:string)
{
	|str1| > 0 && |str2| > 0 && 
	exists x :: (0 <= x < |str1| ==> exists y :: (x < y <= |str1| ==> (isSubstringPredRowanAdjusted(str1[x..y], str2)  && |str1[x..y]| == k)))
}

predicate haveNotCommonKSubstringPredAdjusted(k:nat, str1:string, str2:string)
{
	(|str1| == 0) || (|str2| == 0) || forall x :: !(0 <= x < |str1| ==> exists y :: (x < y <= |str1| ==> (isSubstringPredRowanAdjusted(str1[x..y], str2)  && |str1[x..y]| == k)))
	//TODO: your FOL formula should start with a forall
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemmaAdjusted(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPredAdjusted(k,str1,str2) <==> !haveNotCommonKSubstringPredAdjusted(k,str1,str2)
	ensures !haveCommonKSubstringPredAdjusted(k,str1,str2) <==> haveNotCommonKSubstringPredAdjusted(k,str1,str2)
{}
*/

/********************************************************
	Stefanos Method of K Substring
********************************************************/
predicate haveCommonKSubstringPredStefano(k:nat, str1:string, str2:string) {
	|str1| >= k && |str2| >= k && 
	exists x :: 0 <= x <= (|str1| - k) && isSubstringPredUsingPrefix(str1[x..][..k], str2) 
}

predicate haveNotCommonKSubstringPredStefano(k:nat, str1:string, str2:string) {
	|str1| < k || |str2| < k ||
	forall x :: 0 <= x <= (|str1| - k) ==> isNotSubstringPredUsingPrefix(str1[x..][..k], str2)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemmaStefano(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPredStefano(k,str1,str2) <==> !haveNotCommonKSubstringPredStefano(k,str1,str2)
	ensures !haveCommonKSubstringPredStefano(k,str1,str2) <==> haveNotCommonKSubstringPredStefano(k,str1,str2)
{}
