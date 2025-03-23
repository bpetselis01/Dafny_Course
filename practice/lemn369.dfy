function N369(n: nat): nat
{
    if n == 0 then 0 else 3 * n * n * n + 6 * n
}

lemma {:induction false} LemN369(n: nat)
// n is a natural number then 3 ∗ n ∗ n ∗ n + 6 ∗ n is divisible by 9 for n ≥ 0
requires n >= 0
ensures N369(n) % 9 == 0
{
    // Base Case
    if n == 0 {
        assert N369(n) % 9 == 0 % 9 == 0;
    } else {
        // IH
        LemN369(n - 1);
        var k := N369(n - 1) / 9;
        assert N369(n - 1) == 9*k;
        assert (n - 1) * (n - 1) * (n - 1) + 2 * (n - 1) == 3*k;
        assert n == (3*k - (n - 1) * (n - 1) * (n - 1)) / 2 + 1;
        assert N369(n) == 3*n*n*n + 6*((3*k - (n - 1) * (n - 1) * (n - 1)) / 2 + 1);
        assert N369(n) == 3*n*n*n + (9*k - 3*(n - 1)*(n - 1)*(n - 1)) + 6;
        assert N369(n) == 3*n*n*n + (9*k - 3*(n*n - 2*n + 1)*(n - 1)) + 6;
        assert N369(n) == 3*n*n*n + (9*k - 3*n*n*n + 9*n*n - 9*n + 3) + 6;
        assert N369(n) == 9*k + 9*n*n - 9*n + 9;
        assert N369(n) / 9 == k + n*n - n + 1;
        assert N369(n) % 9 == 0;
    }
}