method main() {

	var s:= "hello";
	assert forall x :: 0 <= x <= |s| ==> s[x..] != "dog";
}


predicate isPrefixPred(pre:string, str:string) {
	0 < |pre| <= |str| && str[..|pre|] == pre
}

predicate isSubstringPred(sub:string, str:string) {
	//(0 < |sub| <= |str|) && exists x :: (0 <= x <= |str| && isPrefixPred(sub, str[x..]))
	(0 < |sub| <= |str|) && (exists x :: (0 <= x < |str| && x != -1)) && isPrefixPred(sub, str)
}

lemma prefixImpliesSubstring(sub:string, str:string)
ensures isPrefixPred(sub, str) ==> isSubstringPred(sub, str)
{}