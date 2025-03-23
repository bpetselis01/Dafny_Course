predicate no42(x:int)                                       // DO NOT CHANGE
requires x!=42                                              // DO NOT CHANGE
{ 0<x<100 }                                                 // DO NOT CHANGE

predicate pete(x:int)                                       // DO NOT CHANGE
requires x != 32 && x != -32                                // specification missing
{ if x>0 then no42(x+10) else no42(10-x) }                  // DO NOT CHANGE

method TruePete(x:int)
requires x < 90 && x > -90 && x != 32 && x != -32
{
    assert pete(x);
}

method FalsePete(x:int)
requires x >= 90 || x <= -90
{
    assert !pete(x);
}
