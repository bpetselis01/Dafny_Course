method Main() {
    var a := 10;
    if a%2==0 { // assumption
        var c := a/2;
        assert 2*c == a;
        assert a*a-2*a+7 == (2*c)*(2*c) - 2*2*c + 7;
        assert a*a-2*a+7 == 2 * (2*c*c-2*c+3) + 1;
        assert ((2*c)*(2*c) - 2*2*c + 7)%2 == 1;
        assert (a*a-2*a+7)%2 == 1;
        // missing line
        assert false;
    }
    assert a%2==1;
}