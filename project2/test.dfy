// Test whether the chain of subsequences works
method Main() {
  var str := "dogcat";
	var sub := "at";
  
  var stop := |str| - |sub|;  // 4 --> stop at 'a'
  var i := 0;
  
  while (i <= stop) {
    print str[i..][..|sub|];
    print "\n";
    i := i+1;
  }
  

  assert str[5..][..1] == str[5..6];
  //assert  (indexed == split);
}

predicate test(x:nat) {
  x == 5
}

predicate test2(x:nat) {
  x > 4 && x < 6
}

lemma lem(x:nat) 
  ensures test(x) <==> test2(x) 
  ensures !test(x) <==> !test2(x)
{}