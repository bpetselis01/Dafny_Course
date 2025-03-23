method DivideBy2(n: int) returns (x: int)
ensures n == 2*x + n % 2
{
    if n % 2 == 0 {
        x := n / 2; 
    } else {
        x := (n - 1) / 2; 
    }
}

method f() returns (x: int) {
    x := 1;
}

method Main() {
    var v := f();
    print "v = ", v, '\n';
}

function TailSizeFunc(a: array<int>) : int
    reads a
    decreases |a|
{
    var n := |a|;
    var count := 0;
    
    var i := 0;
    while i <= n - 1
    invariant 0 <= i <= n - 1
    {
        if a[i] != 0 {
            count := 0;
        } else {
            count := count + 1;
        }

        i := i + 1;
    }
    
    return count;
}