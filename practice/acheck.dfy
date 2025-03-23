predicate acheck(a:array<int>, div:int) reads a
requires a.Length % 2 == 0
requires div >= 1
{
    // index of an element in the array is divisible by n then the element is 0
    forall i :: 0 <= i < a.Length && i % div == 0 ==> a[i] == 0
}

method Validate(){
    var a := new int[6];
    a[0], a[1], a[2], a[3], a[4], a[5] := 0, 42, 0, 42, 0, 42;
    assert acheck(a, 2);

    var b := new int[4];
    b[0], b[1], b[2], b[3] := 0, 1, 2, 3;
    assert acheck(b, 5);
}