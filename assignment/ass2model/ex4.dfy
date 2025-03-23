function pow(x: nat, exp: nat): nat
{if exp == 0 then 1 else x * pow(x, exp - 1)}

// Level 2 Lemma
lemma {:induction false} LemmaPRE(x:nat, m:nat, n:nat)
ensures pow(x, m+n) == pow(x,m) * pow(x,n)
{
    if m == 0 {
        // Base Case
        assert pow(x,m) * pow(x,n) == 1 * pow(x,n);
    } else {
        // IH
        LemmaPRE(x,m-1,n);
    }
}

// lemma {:induction false} LemmaXY(x:nat, y:nat, k:nat)
// requires x > y
// ensures x*pow(y,k) > y*pow(y,k)
// {}

lemma {:induction false} LemmaGRT(x:nat, y:nat, k:nat)
requires x > y
ensures k == 0 ==> pow(x,k) == pow(y,k) == 1
ensures k > 0 ==> pow(x,k) > pow(y,k)
{
    if k == 0 {
        // Base Case
        assert pow(x,k) == pow(y,k) == 1;
    } else {
        // IH
        LemmaGRT(x,y,k-1);

        if k == 1 {
            // Deal with k == 1 case
            assert pow(x,k-1) == pow(y,k-1) == 1;
        } else {
            // Expand IH
            assert pow(x,k-1) > pow(y,k-1);
            // Multiply by x to convert LHS
            assert x*pow(x,k-1) > x*pow(y,k-1);
            // Give Lemma Knowledge
            LemmaPRE(x,k-1,1);
            // Simplify LHS
            assert pow(x,k) > x*pow(y,k-1);
            // Since we know that x & y are > 0, safe assumption
            assert x*pow(y,k-1) >= y*pow(y,k-1);
            LemmaPRE(y,k-1,1);
            assert pow(x,k) >= pow(y,k);
            // Can't be equal, since not the base case
            assert pow(x,k) > pow(y,k);
        }
    }
}


method SystemValidPRE()
{
    var x:nat, k:nat, l:nat;
    LemmaPRE(x,k,l);  // the next assert fails without this lemma
    assert pow(x,k) * pow(x,l) == pow(x, k+l);
}

method ValidGRT()
{
    var x:nat, y:nat, k:nat;
    if x>y {
        LemmaGRT(x,y,k);  // the next asserts fail without this lemma
        assert k==0 ==> pow(x,k)==pow(y,k)==1;
        assert k>0  ==> pow(x,k)>pow(y,k);
    }
}