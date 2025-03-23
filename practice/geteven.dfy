method Geteven(a: array<nat>) modifies a
// Pre-Conditions
// 1. The array may be of any length
requires a.Length > 0

// Post-Conditions
// 1. changes each of the odd elements in a given array into even elements by adding 1 to the odd element
    // a. All odd elements change (added 1)
    // b. All even elements do not change
    // c. Length of a does not change
ensures a.Length == old(a.Length)
ensures forall j :: 0 <= j < a.Length && old(a[j]) % 2 == 0 ==> a[j] == old(a[j])
ensures forall j :: 0 <= j < a.Length && old(a[j]) % 2 == 1 ==> a[j] == old(a[j]) + 1
{
    var i := 0;

    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i && old(a[j]) % 2 == 0 ==> a[j] == old(a[j])
    invariant forall j :: 0 <= j < i && old(a[j]) % 2 == 1 ==> a[j] == old(a[j]) + 1
    invariant forall j :: i <= j < a.Length ==> a[j] == old(a[j])
    {
        if a[i] % 2 == 1 {
            a[i] := a[i] + 1;
        }
        i := i + 1;
    }
}

method Validator() {
    var a:array<nat> := new nat[][0,9,4];
    assert a[0]==0 && a[1]==9 && a[2]==4;
    Geteven(a);
    assert a[0]==0 && a[1]==10 && a[2]==4;
}