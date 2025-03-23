lemma LemCNN(n: nat)
requires n >= 0
ensures n * (n + 1) % 2 == 0
{
    if n * (n + 1) % 2 == 1 {
        if n % 2 == 0 {
            var k := n / 2;
            assert n * (n + 1) == 2*k * (2*k + 1);
            assert n * (n + 1) / 2 == k * (2*k + 1);
            assert n * (n + 1) % 2 == 0;
        } else {
            var k := (n + 1) / 2;
            assert n * (n + 1) == (2*k - 1) * 2*k;
            assert n * (n + 1) / 2 == k * (2*k - 1);
            assert n * (n + 1) % 2 == 0;
        }
        assert false;
    }

    assert n * (n + 1) % 2 == 0;
}