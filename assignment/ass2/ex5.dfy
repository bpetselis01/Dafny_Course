function sumcube(n: nat): nat
{ if n == 0 then 0 else n * n * n + sumcube(n-1) }

function sumton(n: nat): nat
{ if n == 0 then 0 else n + sumton(n-1) }

// Verify sumcube(n - 1) + n^3 == sumcube(n)
lemma {:induction false} LemmaADDCUBE(n: nat)
ensures sumcube(n) + (n+1)*(n+1)*(n+1) == sumcube(n + 1)
{
    if (n == 0) {
        assert sumcube(0) + (0+1)*(0+1)*(0+1) == sumcube(1);
    } else {
        LemmaADDCUBE(n - 1);
    }
}

// Verify sumton(n - 1) * sumton(n - 1) + n^3 == sumton(n) * sumton(n)
lemma {:induction false} LemmaSUMTONSQUARE(n: nat)
ensures sumton(n) * sumton(n) + (n+1)*(n+1)*(n+1) == sumton(n + 1) * sumton(n + 1)
{
    if (n == 0) {
        assert sumton(0) * sumton(0) + (0+1)*(0+1)*(0+1) == sumton(1) * sumton(1);
    } else {
        LemmaSUMTONSQUARE(n - 1);
    }
}

// Verify sumton(n) == n * (n + 1) / 2
lemma {:induction false} LemmaSUMTONFORMULA(n: nat)
ensures sumton(n) == n * (n + 1) / 2
{
    if n == 0 {
        assert sumton(0) == 0;
        assert 0 == 0 * (0 + 1) / 2;
    } else {
        LemmaSUMTONFORMULA(n - 1);
    }
}

lemma {:induction false} LemmaCUBE(n: nat)
ensures sumcube(n) == (sumton(n)) * (sumton(n)) 
{
    if (n == 0) {
        assert sumcube(n) == sumton(n) * sumton(n) == sumton(0) * sumton(0) == 0;
    } else {
        LemmaCUBE(n - 1);
        LemmaSUMTONFORMULA(n - 1);
        LemmaADDCUBE(n - 1);
        LemmaSUMTONSQUARE(n - 1);
        assert sumton(n - 1) * sumton(n - 1) == sumcube(n - 1);
        // LemmaADDCUBE handles RHS & LemmaSUMTONSQUARE handles LHS
        assert sumton(n - 1) * sumton(n - 1) + n*n*n == sumcube(n - 1) + n*n*n;
        assert sumton(n) * sumton(n) == sumcube(n);
    }
}