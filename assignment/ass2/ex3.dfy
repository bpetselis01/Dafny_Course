predicate growtail(a: array<int>, indx:int) reads a
requires -1 <= indx < a.Length
{
    forall j :: indx < j < a.Length ==> a[j] == -1
}

method Newtail(a: array<int>) returns (size: nat) modifies a
requires a.Length > 0
ensures 0 <= size <= a.Length
ensures a[a.Length - 1] != -1 ==> size == 0
ensures 0 <= size < a.Length ==> a[a.Length - 1 - size] != 0
ensures growtail(a, a.Length - 1 - size)
{
    var i:int := a.Length - 1;
    while i >= 0 && a[i] == 0
    invariant -1 <= i < a.Length
    invariant growtail(a, i)    
    {
        a[i] := -1;
        i := i - 1;
    }
    size := a.Length - (i + 1);
}

method Validate() {

    var b: array<int> := new int[][1, 2, 3, 9, 2, 0, 0, 0, 0, 0, 0, 8];
    var c: array<int> := new int[][0, 0, 0, -1];
    var d: array<int> := new int[][0];
    var e: array<int> := new int[][0, 42, 0];
    assert e[0] == 0 && e[1] == 42 && e[2] == 0;
    var f: array<int> := new int[][0, 0, 0];
    assert f[0] == 0 && f[1] == 0 && f[2] == 0;
    var g: array<int> := new int[][-1, 0, 0, 0, 0, 0, 0];
    assert g[0] == -1 && g[1] == 0 && g[2] == 0 && g[3] == 0 && g[4] == 0 && g[5] == 0 && g[6] == 0;

    var a := new int[][0,42,0];
    assert a[0] == 0 && a[1] == 42 && a[2] == 0;
    var s:nat := Newtail(a);
    // assert s == 1;
    // assert a[0] == 0 && a[1] == 42 && a[2] == -1;

    var Newtail2 := Newtail(b);
    // assert Newtail2 == 0;

    var Newtail3 := Newtail(c);
    // assert Newtail3 == 0;

    var Newtail4 := Newtail(d);
    // assert Newtail4 == 1;
    // assert d[0] == -1;

    var Newtail5 := Newtail(e);
    // assert Newtail5 == 1;
    // assert e[0] == 0 && e[1] == 42 && e[2] == -1;

    var Newtail6 := Newtail(f);
    // assert Newtail6 == 3;

    var Newtail7 := Newtail(g);
    // assert Newtail7 == 6;
}
