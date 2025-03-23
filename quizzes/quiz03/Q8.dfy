method Reverse(s: string)
decreases |s|
{
    if s!= [] {
        Reverse(s[1..]);
        print s[0];
    }
}

method Main() {
    var myString := "Hello, Dafny!";
    Reverse(myString);
}