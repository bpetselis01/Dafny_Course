method Main() {
    var x:int;
    var s: set<int> := {1, 2, 3, 4, 5};

    while |s|>0
    decreases |s|
    {x :| x in s;}
    assert x != 42;
}
