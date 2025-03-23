function Div2(n: nat): nat 
{
    if n == 0 then 0 else (n*n - n)
}

lemma {:induction false} LemmaDiv2(n: nat)
requires n >= 0
ensures Div2(n) % 2 == 0
{
    // Base Case
    if n == 0 {
        assert Div2(n) % 2 == 0 % 2 == 0;
    } else {
        // IH
        LemmaDiv2(n - 1);
    }
}