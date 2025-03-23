method f() returns (x: int) {
    x := 1;
}

method Main() {
    var v := f();
    print "v = ", v, '\n';
}