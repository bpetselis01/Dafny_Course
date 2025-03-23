method Hash(z: nat) modifies this.buf, this`shadow
requires Valid()
requires 1 <= z <= |shadow|
requires 0 <= m + z - 1 <= n <= buf.Length

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

// Pop # Bottom
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

// Pop # Middle
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

// Pop # Top
method YetAnotherValidator() 
{
   var q := new Quack(7); // plenty of room
   q.Push('A');
   q.Push('B');
   q.Push('C');
   q.Push('D');
   q.Hash(4);             // zap A at location 1

   var c : char;
   c := q.Pop(); assert c == '#'; // top element
   c := q.Pop(); assert c == 'C'; // top element
   c := q.Qop(); assert c == 'A'; // bottom element
   c := q.Pop(); assert c == 'B'; // last element

   var e: bool;
   e := q.Empty(); assert e; // check empty
}