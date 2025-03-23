// If idx != -1, all elements in array should be less than to max
predicate oneMax(s: seq<int>, idx: int, max: int, i: int)
requires 0 <= i <= |s| && idx != -1
{
    0 <= idx < i && 
    forall j| 0 <= j < i :: s[idx] >= s[j] &&
    exists j| 0 <= j < i :: max == s[j] &&
    s[idx] == max
}

// If idx == -1, all elements in array should be less than or equals to max
predicate mulMax(s: seq<int>, idx: int, max: int, i: int)
requires 0 <= i <= |s| && idx == -1
{
    forall j| 0 <= j < i :: max >= s[j] &&
    exists j| 0 <= j < i :: max == s[j]
}

method Strictmax(s: seq<int>) returns (max: int, idx: int)
requires |s| > 0
ensures idx == -1 ==> mulMax(s, idx, max, |s|)
ensures idx != -1 ==> oneMax(s, idx, max, |s|)
{
    max := s[0];
    idx := 0;

    var i: int := 1;

    while i < |s|
    invariant 0 <= i <= |s|
    invariant idx == -1 ==> mulMax(s, idx, max, i)
    invariant idx != -1 ==> oneMax(s, idx, max, i)
    {
        if s[i] > max {
            idx := i;
            max := s[i];
        } 
        else if s[i] == max {
            idx := -1;
        }
        i := i + 1 ;
    }
}

method Validator()
{
    var s1 : seq<int> := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    assert s1[14] == 15 && s1[13] == 14 && s1[12] == 13 && s1[11] == 12 && s1[10] == 11 
        && s1[9] == 10 && s1[8] == 9 && s1[7] == 8 && s1[6] == 7 && s1[5] == 6 
        && s1[4] == 5 && s1[3] == 4 && s1[2] == 3 && s1[1] == 2 && s1[0] == 1;
    var s2 : seq<int> := [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
    assert s2[0] == 15;
    var s3 : seq<int> := [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15];
    var s4 : seq<int> := [15, 1, 15, 2, 15, 3, 15, 4, 15, 5, 15, 6, 15, 7, 15];
    var s5 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    
    var max1, idx1: int;
    max1, idx1 := Strictmax(s1);
    assert max1 == 15; 
    // assert idx1 == 14;

    var max2, idx2: int;
    max2, idx2 := Strictmax(s2);
    assert max2 == 15;
    // assert idx2 == 0;

    var max3, idx3: int;
    max3, idx3 := Strictmax(s3);
    // assert max3 == 15;
    // assert idx3 == -1;

    var max4, idx4: int;
    max4, idx4 := Strictmax(s4);
    // assert max4 == 15 && idx4 == -1;

    var max5, idx5: int;
    max5, idx5 := Strictmax(s5);
    // assert max5 == 0 && idx5 == 0;
}

method Main() {
    Validator();
}