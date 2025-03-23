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

function Div6(n: nat): nat
{
    if n == 0 then 0 else (n*n*n - n)
}

lemma {:induction false} LemmaDiv6(n: nat)
requires n >= 0
ensures Div6(n) % 6 == 0
{
    if n == 0 {
        assert Div6(n) % 6 == 0 % 6 == 0;
    } else {
        LemmaDiv6(n - 1);
        assert Div6(n - 1) % 6 == 0;
        var k := ((n-1)*(n-1)*(n-1) - n + 1) / 6;
        assert n == ((n-1)*(n-1)*(n-1) + 1) - 6*k;
        assert Div6(n) == n*n*n - ((n-1)*(n-1)*(n-1) + 1) + 6*k;
        assert Div6(n) == 3*n*n - 3*n + 6*k;
        assert Div6(n) == 3*(n*n - n) + 6*k;
        LemmaDiv2(n);
        assert Div6(n) == 3*(Div2(n)) + 6*k;
        assert Div6(n) == 6*(Div2(n)/2) + 6*k;
        assert Div6(n) == 6*(Div2(n)/2 + k);
        assert Div6(n) / 6 == Div2(n)/2 + k;
        assert Div6(n) % 6 == 0;
    }
}