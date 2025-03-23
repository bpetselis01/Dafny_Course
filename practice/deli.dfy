method Deli(a: array<char>, i: nat) modifies a
requires a.Length > 0
requires 0 <= i < a.Length
// ensures changeDeli(a, i)
ensures forall k :: 0 <= k < i ==> a[k] == old(a[k])
ensures forall j :: i <= j < (a.Length - 1) ==> a[j] == old(a[j + 1])
ensures a[a.Length - 1] == '.'
{
    var del := i;

    // [’b’,’r’,’o’,’o’,’m’] and if del == 1
    // a[1] := a[2] ... a[3] := a[4]
    while del < (a.Length - 1)
    invariant i <= del < a.Length
    // everything before doesn't change
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j])
    // everything after has been shifted
    invariant forall j :: i <= j < del ==> a[j] == old(a[j + 1])
    // everything after remains the same
    invariant forall j :: del <= j < a.Length ==> a[j] == old(a[j])
    {
        a[del] := a[del + 1];
        del := del + 1;
    }
    a[a.Length - 1] := '.';
}


method Validate() {
    var z := new char[]['b','r','o','o','m'];
    assert z[0] == 'b';
    Deli(z, 1);

    print z[0];
    print z[1];
    print z[2];
    print z[3];
    print z[4];

    // assert z[..] == "boom.";

    var a := new char[]['b'];
    Deli(a, 0);

    print a[0];
}

method Main() {
    Validate();
}