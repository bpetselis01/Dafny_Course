method SumTon(n:int) returns (s:int)
requires n >= 0
ensures s == n*(n+1)/2
{
    var k := 0;
    s := 0;
    while k <= n
    invariant 0<=k<=n+1 && s==(k-1)*k/2
    {
        s := s + k;
        k := k + 1;
    }
}

method SumTonDown(n:int) returns (s:int)
requires n >= 0
ensures s == n*(n+1)/2
{
    var k := n;
    s := 0;
    while k > 0
    invariant 0<=k<=n
    invariant s == (n+k)*(n-k+1)/2 - k
    {
        s := s + k;
        k := k - 1;
    }
}

method Main() {
    var a := SumTon(9);
    var b := SumTonDown(5);
    assert b == 15;
}