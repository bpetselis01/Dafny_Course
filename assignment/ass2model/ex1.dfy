method Fastmul(x:nat, y:nat) returns (product:nat)
ensures product == x*y
{
    var halvx := x;
    var douby := y;
    var prod := 0;

    while halvx != 0
    invariant prod == x * y - halvx * douby
    invariant halvx >= 0
    invariant douby >= 0
    decreases halvx
    {                
        if halvx % 2 == 1 { 
            prod := prod + douby; 
        }    
        halvx := halvx / 2;
        douby := douby * 2;
    }
    product := prod;
}

method Validator()
{
    // 1: Even, 2: Even
    var x := 42;
    var y := 10;
    var product := Fastmul(x,y);
    assert product == 420;

    // 1: Even, 2: Odd
    x := 42;
    y := 17;
    product := Fastmul(x,y);
    assert product == 714;

    // 1: Odd, 2: Even
    x := 41;
    y := 17;
    product := Fastmul(x,y);
    assert product == 697;

    // 1: Odd, 2: Odd
    x := 41;
    y := 71;
    product := Fastmul(x,y);
    assert product == 2911;

    // 1: Even Large, 2: Even Large
    x := 42002;
    y := 10004;
    product := Fastmul(x,y);
    assert product == 420188008;

    // 1: Even, 2: Odd
    x := 42002;
    y := 1711;
    product := Fastmul(x,y);
    assert product == 71865422;

    // 1: Odd, 2: Even
    x := 42001;
    y := 10004;
    product := Fastmul(x,y);
    assert product == 420178004;

    // 1: Odd, 2: Odd
    x := 40001;
    y := 7001;
    product := Fastmul(x,y);
    assert product == 280047001;

    x := 1;
    y := 10;
    product := Fastmul(x,y);
    assert product == 10;
    
    x := 1;
    y := 11;
    product := Fastmul(x,y);
    assert product == 11;

    x := 0;
    y := 11;
    product := Fastmul(x,y);
    assert product == 0;

    x := 0;
    y := 11;
    product := Fastmul(x,y);
    assert product == 0;
}

method Main() {
    Validator();
}