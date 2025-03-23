////////////////////////////////////////////////////////////////////////
     2	// EXERCISE 2                                                   10 MARKS
     3	/////////////
     4	
     5	// returns the maximum element in a sequence, called max
     6	// if max is a strict max, idx is its index, else the max element is duplicated and idx=-1
     7	
     8	predicate only1(s: seq<int>, idx:nat, lim:nat, m:int) // m is a strict max in s[0..lim]
     9	requires 0<=idx<|s|
    10	requires 0<=lim<=|s|
    11	{
    12	   s[idx] == m && (forall j:: 0<=j<lim && j!=idx ==> m>s[j])
    13	}
    14	
    15	predicate more1(s: seq<int>, lim:nat, m:int)
    16	requires 0<=lim<=|s|
    17	{
    18	   exists j,k:: 0<=j<k<lim && s[j]==s[k]==m && (forall l:: 0<=l<lim ==> m>=s[l])
    19	}
    20	
    21	method Strictmax(s: seq<int>) returns(max:int, idx:int)
    22	requires |s| > 0
    23	ensures idx==-1 || 0<=idx<|s|
    24	ensures if idx==-1 then more1(s, |s|, max) else only1(s, idx, |s|, max)
    25	{
    26	   idx := 0;
    27	   max := s[idx];
    28	   var i := 1;
    29	   while i<|s|
    30	   invariant -1<=idx<i<=|s|
    31	   invariant if idx==-1 then more1(s, i, max) else only1(s, idx, i, max)
    32	   decreases |s|-i 
    33	   {
    34	      if s[i] >= max {
    35	         if s[i]==max { idx := -1; } // repeat max, idx negative
    36	         else { idx := i; }          // a new max, idx is its index
    37	         max := s[i];
    38	      }
    39	      i := i + 1;
    40	   }
    41	}