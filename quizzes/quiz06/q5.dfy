method Setup () returns (a: array<char>)
ensures fresh(a)
ensures a.Length == 42
{ 
    a := new char[42];
}

method Main() {
    var b := Setup();
    b[10] := 'x';
}