method taut(a:bool, b: bool, c: bool)
{
    assert ((a ==> (b || c)) || (b ==> a)) || (c ==> a);
}

method Main() {
    taut(true,false,false);
    taut(true,true,false);
    taut(true,true,true);
    taut(false,false,false);
    taut(false,true,false);
    taut(false,true,true);
    taut(true,false,true);
    taut(false,false,true);
}