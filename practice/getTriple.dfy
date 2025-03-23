predicate readTriple(a: array<int>, index: int) reads a
requires 0 <= index < a.Length - 2
{
    a[index] == a[index + 1] == a[index + 2]
}

predicate containsTriple(a: array<int>) reads a
{
    exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

method GetTriple(a: array<int>) returns (index: int)
requires a.Length >= 0
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures 0 <= index < a.Length - 2 <==> containsTriple(a)
ensures 0 <= index < a.Length - 2 ==> readTriple(a, index)
ensures index == a.Length ==> forall i :: 0 <= i < a.Length - 2 ==> a[i] != a[i + 1] || a[i + 1] != a[i + 2]
{
    if a.Length < 3 { return a.Length; }

    var i := 0;
    while i < a.Length - 2
    invariant 0 <= i <= a.Length - 2
    invariant forall j :: 0 <= j < i ==> a[j] != a[j + 1] || a[j + 1] != a[j + 2]
    {
        if a[i] == a[i + 1] == a[i + 2] {
            return i;
        }
        i := i + 1;
    }
    return a.Length;
}

// returns with the index of the first triple of consecutive, identical
// elements in an array of integers
// 1. 0 <= index < a.Length ==> a[index] == a[index + 1] == a[index + 2]

// If there is no triple in the array then the method returns the length of the array
// 2. index == a.Length ==> forall i :: 0 <= i < index ==> a[i] != a[i + 1] || a[i + 1] != a[i + 2]

// The array may be any length
// 1. requires a.Length >= 0 

// The index of a triple is simply the index of the first of the three elements.
// 1. 

// A series of tests of GetTriple
method TesterGetTriple()
{
    var a: array<int> := new int[1][42];
    assert a[0] == 42;
    var b := GetTriple(a);
    assert b==a.Length;   // NO TRIPLE

    a := new int[2][42,42];
    assert a[0] == a[1] == 42;
    b := GetTriple(a);
    assert b==a.Length;   // NO TRIPLE

    a := new int[3][42,42,0];
    assert a[0] == a[1] == 42 && a[2] == 0;
    b := GetTriple(a);
    assert b==a.Length;   // NO TRIPLE

    a := new int[4][42,42,0,42];
    assert a[0] == a[1] == a[3] == 42 && a[2] == 0;
    b := GetTriple(a);
    assert b==a.Length;   // NO TRIPLE

    a := new int[3][42,42,42];
    assert a[0] == a[1] == a[2] == 42;
    b := GetTriple(a);
    assert b==0;         // A TRIPLE!

    a := new int[4][0,42,42,42];
    assert a[0] == 0 && a[1] == a[2] == a[3] == 42;
    b := GetTriple(a);
    assert b==1;         // A TRIPLE!

    a := new int[6][0,0,42,42,42,0];
    assert a[0] == a[1] == a[5] == 0 && a[2] == a[3] == a[4] == 42;
    b := GetTriple(a);
    assert b==2;         // A TRIPLE!
}