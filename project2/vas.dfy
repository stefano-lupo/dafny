predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}


// Build each substring of length |sub| by walking through the sequence
predicate isSubstringPred(sub:string, str:string)
{
  |sub| <= |str| && |sub| > 0 && 
		exists x :: (0 <= x <= (|str|-|sub|) ==> exists y :: (y == (|sub| + x) ==> str[x..y]==sub)) 
}

// Same thing just without needing to explicitly define y
predicate isSubstringPredChainSubs(sub:string, str:string) {
	|sub| <= |str| && |sub| > 0 && 
		exists x :: 0 <= x <= (|str|-|sub|) && (str[x..][..|sub|]) == sub
}

// Same thing using prefix method
predicate isSubstringPredPrefix(sub:string, str:string) {
		exists x :: 0 <= x <= (|str|-|sub|) && isPrefixPred(sub, str[x..])
}

lemma test2(str:string, x:nat, y:nat)
requires x >= 0 && x < |str| &&  (x+y) >= 0 && (x+y) < |str|
ensures str[x..y+x] == str[x..][..y]
{}

// Rustan Leino -- Verification Corner - Writing inductive proofs
// Rustan leino imperial and Sofia Drossopoulou

lemma test(sub:string, str:string)

  // Right and chain subs
  //ensures isSubstringPredChainSubs(sub, str) ==> isSubstringPred(sub, str) 
  //ensures isSubstringPred(sub, str) <==> isSubstringPredChainSubs(sub, str) 

  // Right and prefix call
  //ensures isSubstringPred(sub, str) ==> isSubstringPredPrefix(sub, str)
  ensures isSubstringPredPrefix(sub, str) ==> isSubstringPred(sub, str) 
  //ensures isSubstringPred(sub, str) <==> isSubstringPredPrefix(sub, str) 

  // Chain Subs and Prefix call
  //ensures isSubstringPredChainSubs(sub, str) ==> isSubstringPredPrefix(sub, str)
  //ensures isSubstringPredPrefix(sub, str) ==> isSubstringPredChainSubs(sub, str) 
  //ensures isSubstringPredChainSubs(sub, str) <==> isSubstringPredPrefix(sub, str) 
{
}

predicate isNotSubstringPred(sub:string, str:string)
{
	|sub| > |str| || |sub| == 0 || |str| == 0  || 
		forall x :: !(0 <= x <= (|str|-|sub|) ==> 
    exists y :: (y == (|sub| + x) ==> str[x..y]==sub))
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures  isSubstringPredPrefix(sub,str) <== !isNotSubstringPred(sub,str)
	//ensures !isSubstringPredPrefix(sub,str) <==>  isSubstringPredPrefix(sub,str)
{}
