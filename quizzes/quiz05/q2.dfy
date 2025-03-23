lemma LemIAmSingle(s:set<int>, i:int) 
// requires |s|==1 && i in s
requires |s|==1 && i in s
ensures s=={i}
{
    if s>{i} {
        assert |s-{i}|>=1 ==> |s|>1;
        assert |s|==1 && |s|>1;
        assert false;
    }
}

method GValidation()
{
    var s:set<int>;
    var i:int;
    if |s|==1 && i in s {
        LemIAmSingle(s,i);
        assert s=={i};
    }
}

method Main() {
    GValidation();
}
