method ZeroArray(a: array<int>) modifies a
ensures forall x :: 0 <= x < a.Length ==> a[x] == 0
{
    var ind := 0;
    while ind < a.Length
    invariant forall x :: 0 < x < ind ==> a[x] == 0
    {
        a[ind] := 0;
        ind := ind + 1;
    }
}

method Main() {
    var a := new int[][1,2,3,4,5,6,7,8,9];
    ZeroArray(a);
}