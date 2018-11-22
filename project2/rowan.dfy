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


predicate isSubstringPred(sub:string, str:string)
{
  (|sub| <= |str|) && (|sub| > 0) && 
		exists x :: (0 <= x <= (|str|-|sub|) ==> exists y :: (y == (|sub| + x) ==> str[x..y]==sub)) 
  // Exists and x for each "position" of the substring
  // Exists y because str[x..x+|sub|] won't work with Dafny
}

predicate isSubstringPred2(sub:string, str:string) {
	(|sub| <= |str|) && (|sub| > 0) && 
		exists x :: 0 <= x <= (|str|-|sub|) ==> str[x..][..|sub|] == sub
}

predicate isSubstringPred3(sub:string, str:string) {
	(|sub| <= |str|) && (|sub| > 0) && 
		exists x :: 0 <= x <= (|str|-|sub|) ==> isPrefixPred(sub, str[x..])
}

lemma test(sub:string, str:string) ensures
	isSubstringPred2(sub, str) <==> isSubstringPred3(sub, str) 
{}

predicate isNotSubstringPred(sub:string, str:string)
{
	!(|sub| <= |str|) || (|sub| == 0) || (|str| == 0)  || 
		forall x :: !(0 <= x <= (|str|-|sub|) ==> exists y :: (y == (|sub| + x) ==> str[x..y]==sub))
	//TODO: your FOL formula should start with a forall
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	(|str1| != 0) && (|str2| != 0) && exists x :: (0 <= x < |str1| ==> exists y :: (x < y <= |str1| ==> (isSubstringPred(str1[x..y], str2)  && |str1[x..y]| == k)))
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	(|str1| == 0) || (|str2| == 0) || forall x :: !(0 <= x < |str1| ==> exists y :: (x < y <= |str1| ==> (isSubstringPred(str1[x..y], str2)  && |str1[x..y]| == k)))
	//TODO: your FOL formula should start with a forall
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}