// Exponential Function
function exp(x: nat, n: nat): nat
{
    if n == 0 then 1
    else x * exp(x, n - 1)
}

// Level 2 Lemma for Product Rule of Exponentiation 
lemma {:induction false} LemmaPRE(x:nat, m:nat, n:nat)
decreases m
ensures exp(x, m + n) == exp(x, m) * exp(x, n)
{
    if (m == 0 && n != 0) {
        assert exp(x, m) * exp(x, n) == exp(x, n);
    } else if (n == 0 && m != 0) {
        assert exp(x, m) * exp(x, n) == exp(x, m);
    } else if (n == 0 && m == 0) {
        assert exp(x, m + n) == exp(x, 0);
        assert exp(x, 0) == 1;
    } else {
        LemmaPRE(x, m - 1, n);
    }
}

// Level 3 Lemma for “Greater-Than” Rule of Exponentiation
// Uses LemmaPRE
lemma {:induction false} LemmaGRT(x:nat, y:nat, k:nat)
requires x > y
requires k >= 0 
ensures k == 0 ==> exp(x, k) == exp(y, k)
ensures k > 0 ==> exp(x, k) > exp(y, k)
{
    if (k == 0) {
        assert exp(x, k) == exp(y, k);
    } else if (k > 0) {
        LemmaGRT(x, y, k - 1);
        LemmaPRE(x, k - 1, 1);
        assert exp(x, k - 1) >= exp(y, k - 1);
    } else {
        assert false;
    }
}

method ValidatorPRE()
{
    LemmaPRE(2, 3, 4);
    assert exp(2, 3 + 4) == exp(2, 3) * exp(2, 4);

    LemmaPRE(5, 6, 7);
    assert exp(5, 6 + 7) == exp(5, 6) * exp(5, 7);

    LemmaPRE(100, 0, 0);
    assert exp(100, 0 + 0) == exp(100, 0) * exp(100, 0);

    LemmaPRE(10, 10, 0);
    assert exp(100, 10 + 0) == exp(100, 10) * exp(100, 0);

    LemmaPRE(10, 0, 10);
    assert exp(100, 0 + 10) == exp(100, 0) * exp(100, 10);
}

method ValidatorGRT()
{
    LemmaGRT(3, 2, 4);
    assert exp(3, 4) > exp(2, 4);

    LemmaGRT(5, 4, 6);
    assert exp(5, 6) > exp(4, 6);

    LemmaGRT(5, 4, 0);
    assert exp(5, 0) == exp(4, 0);
}

method Main() {
    ValidatorPRE();
    ValidatorGRT();
}