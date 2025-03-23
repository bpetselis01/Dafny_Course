class Quack  /* DO NOT CHANGE ANYTHING IN THIS CLASS   */
{            /* APART FROM THE ADDITION OF METHOD HASH */
    var buf:array<char>;
    var m:int, n:int;

    ghost var shadow: seq<char>;

    predicate Valid() reads this, this.buf
    { buf.Length!=0 && 0<=m<=n<=buf.Length && shadow==buf[m..n] }

    //////////////////////
    constructor(size: int)
    requires size > 0
    ensures shadow == []
    ensures fresh(buf)
    ensures Valid()
    {
        buf := new char[size];
        m, n:= 0, 0;
        shadow:= [];
    }

    ////////////////////////////////
    method Empty() returns (x: bool)
    requires Valid()
    ensures x <==> shadow==[] // an empty shadow means x is true
    ensures Valid()
    {
       x := m==n;             // no elements means x is true
    }      

    ////////////////////////////////////////////
    method Push(x: char) modifies this, this.buf
    requires Valid()
    // code
    ensures if old(n)   == old(buf.Length) then fresh(buf) else buf==old(buf)
    ensures if old(n-m) == old(buf.Length) then buf.Length==2*old(buf.Length)
                                           else buf.Length==old(buf.Length)
    // shadow
    ensures |shadow|    == |old(shadow)|+1
    ensures   shadow    == old(shadow) + [x]; // new tail
    ensures Valid()
    {
        if n==buf.Length
        {
            var nu:= new char[buf.Length];           // temporary
            if m==0 { nu := new char[2*buf.Length]; }// double size
            forall (i | 0<=i<n-m) { nu[i]:= buf[m+i]; } // copy m..n to 0..n-m
            buf, m, n:= nu, 0, n-m;                  // reset buf, m, n
        }
        buf[n], n:= x, n+1;         // now we definitely have room
        shadow:= shadow + [x];      // concat shadow and 'x
    }   

    //////////////////////////////////////////////////////////
    method Pop() returns(x: char) modifies this`shadow, this`n
    requires Valid()
    requires  n-m >= 1                            // at least 1 element on the quack
    // code
    ensures   buf    == old(buf)                  // buf name does not change 
    ensures   x      == old(buf[n-1])             // element n-1 is returned
    ensures   n      == old(n-1)                  // n moves down
    // shadow
    ensures |shadow| == |old(shadow)|-1           // popped an elem
    ensures   x      == old(shadow[|shadow|-1])   // last element
    ensures shadow   == old(shadow[..|shadow|-1]) // chop off tail
    ensures Valid()                               // check okay at end
    {
        x, n := buf[n-1], n-1;                    // get tail, decr n
        shadow:= shadow[..|shadow|-1];            // chop tail off shadow
    }

    //////////////////////////////////////////////////////////
    method Qop() returns(x: char) modifies this`shadow, this`m
    requires Valid()
    requires n-m >= 1;                            // at least 1 element on the quack
    // code
    ensures buf      == old(buf)                  // no change in name
    ensures   x      == old(buf[m])               // element m is returned
    ensures   m      == old(m+1)                  // m moves up
    // shadow
    ensures |shadow| == |old(shadow)|-1           // qopped an elem
    ensures   x      == old(shadow[0])            // first elem
    ensures shadow   == old(shadow[1..])          // chop off head
    ensures Valid()
    { 
        x, m:= buf[m], m+1;
        shadow:= shadow[1..];
    }

    // D O  N O T  C H A N G E  A N Y T H I N G  A B O V E  T H I S  L I N E
    /////////////////////////////////////////////////////////////////////
    //
    // METHOD HASH CODE GOES HERE
    //
    /////////////////////////////////////////////////////////////////////

    method Hash(z: nat) modifies this.buf, this`shadow
    requires Valid()
    requires n - m >= 1;
    requires 1 <= z <= |shadow|
    requires 0 <= m + z - 1 <= n <= buf.Length

    ensures buf == old(buf)
    ensures buf.Length == old(buf.Length)
    ensures buf[..(m + z - 1)] == old(buf[..(m + z - 1)])
    ensures buf[(m + z)..] == old(buf[(m + z)..])
    ensures buf[m + z - 1] == '#'

    ensures |shadow| == |old(shadow)|
    ensures shadow[..(z - 1)] == old(shadow[..(z - 1)])
    ensures shadow[z..] == old(shadow[z..])
    ensures shadow[z - 1] == '#'

    ensures Valid()
    {
        var idx := m + z - 1;

        if 0 <= idx < n {
            buf[idx] := '#';
            shadow := shadow[(z - 1) := '#'];
        }
    }
    
} // end of Quack class

method BasicValidator() // YOU MAY CHANGE THE VALIDATOR
{
   var q := new Quack(5); // plenty of room
   q.Push('A');
   q.Push('B');
   q.Push('C');
   q.Hash(1);             // zap A at location 1

   var c : char;
   c := q.Pop(); assert c == 'C'; // top element
   c := q.Qop(); assert c == '#'; // bottom element
   c := q.Pop(); assert c == 'B'; // last element

   var e: bool;
   e := q.Empty(); assert e; // check empty
}

method AnotherValidator() 
{
   var q := new Quack(7); // plenty of room
   q.Push('A');
   q.Push('B');
   q.Push('C');
   q.Push('D');
   q.Hash(2);             // zap A at location 1

   var c : char;
   c := q.Pop(); assert c == 'D'; // top element
   c := q.Pop(); assert c == 'C'; // top element
   c := q.Qop(); assert c == 'A'; // bottom element
   c := q.Pop(); assert c == '#'; // last element

   var e: bool;
   e := q.Empty(); assert e; // check empty
}