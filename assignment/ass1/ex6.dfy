// method TailSizeOld(a: array<int>) returns (count: int)
// requires a.Length > 0
// ensures count == find(a, a.Length - 1)
// ensures 0 <= count <= a.Length
// {
//     count := 0;
   
//    var i := 0;
//    while i <= a.Length - 1
//    invariant 0 <= i <= a.Length
//    {
//        if a[i] != 0 {
//            count := 0;
//        } else {
//            count := count + 1;
//        }

//        i := i + 1;
//    }
// }

function find(a:array<int>, i:int): int reads a
requires 0<=i<a.Length
{
    if i == 0 then 0
    else if a[i] == 0 then find(a, i - 1) + 1
    else 0
}

method TailSize(a: array<int>) returns (count: int)
requires a.Length > 0
ensures count == find(a, a.Length - 1)
ensures 0 <= count <= a.Length
ensures forall j :: a.Length - count <= j < a.Length ==> a[j] == 0
{
    count := 0;
    var i := a.Length - 1;
    
    while i >= 0 && a[i] == 0
    invariant 0 <= i + 1 <= a.Length
    invariant count + i + 1 == a.Length
    invariant forall j :: a.Length - count <= j < a.Length ==> a[j] == 0
    decreases i
    {
        count := count + 1;
        i := i - 1;
    }
}

method Validate() {
    var a: array<int> := new int[][42];
    var b: array<int> := new int[][1, 2, 3, 9, 2, 0, 0, 0, 0, 0, 0, 8];
    var c: array<int> := new int[][0, 0, 0, -1];
    var d: array<int> := new int[][0];
    var e: array<int> := new int[][0, 42, 0];
    var f: array<int> := new int[][0, 0, 0];
    var g: array<int> := new int[][-1, 0, 0, 0];
    var h: array<int> := new int[][-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0];
    var i: array<int> := new int[][-1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    var j: array<int> := new int[][-1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0];

    var tailSize1 := TailSize(a);
    assert tailSize1 == 0;

    var tailSize2 := TailSize(b);
    assert tailSize2 == 0;

    var tailSize3 := TailSize(c);
    assert tailSize3 == 0;

    var tailSize4 := TailSize(d);
    assert tailSize4 == 1;

    var tailSize5 := TailSize(e);
    assert tailSize5 == 1;

    var tailSize6 := TailSize(f);
    assert tailSize6 == 3;

    var tailSize7 := TailSize(g);
    assert tailSize7 == 3;

    var tailSize8 := TailSize(h);
    assert tailSize8 == 5;

    var tailSize9 := TailSize(i);
    assert tailSize9 == 12;

    var tailSize10 := TailSize(j);
    assert tailSize10 == 1;
}

method Main() {
    Validate();
}