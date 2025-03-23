method Main() {
    var b: string := "xy";
    var n: int := 0;
    var m: int := 1;
    b := b[0 := b[1]];
    b := b[1 := b[0]];
    n, m := m, n;

    print "b: ", b, '\n';
    print "n: ", n, '\n';
    print "m: ", m, '\n';
}
