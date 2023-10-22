method RotateLeft(a: array) // tute example
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)])
    ensures a[a.Length -1] == old(a[0])
{
    var n := 0;
    
    while n != a.Length-1
        invariant 0 <= n <= a.Length - 1
        invariant forall i :: 0 <= i < n ==> a[i] == old(a[i+1])
        invariant a[n] == old(a[0])
        invariant forall i :: n < i <= a.Length-1 ==> a[i] == old(a[i])

    {
        a[n], a[n+1] := a[n+1],a[n];
        n := n + 1;
    }
}

method RotateLeftSadra(a: array) // Author: Sadra
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[(i + 1) % a.Length])
{
    var n := a.Length - 1;
    while n != 0
        invariant 0 <= n <= a.Length - 1
        invariant forall i :: n < i < a.Length - 1 ==> a[i] == old(a[(i + 1)])
        invariant forall i :: 0 < i <= n ==> a[i] == old(a[i])   
        invariant n == a.Length - 1 ==> a[0] == old(a[0]) && a[a.Length - 1] == old(a[a.Length - 1])
        invariant n < a.Length - 1 ==> a[0] == old(a[n + 1]) && a[a.Length - 1] == old(a[0])

    {

        a[n] , a[0] := a[0], a[n];
        n := n - 1;
    }
}

function Wrap(x: int, n: int): int
  requires 0 <= x <= n
{
  if x == n then 0 else x
}

method RotateLeftCait(a: array) // Author:Cait
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[(i+1)%a.Length])
{
    var n := a.Length - 1;
    while n != 0
        invariant 0 <= n <= a.Length - 1
        invariant forall i :: 
    1 <= i <= n ==> a[i] == old(a[i])
        invariant forall i :: 
    n < i < a.Length ==> a[i] == old(a[Wrap(i+1, a.Length)])
        invariant a[0] == old(a[Wrap(n+1, a.Length)])
    {
        a[0], a[n] := a[n], a[0];
        n := n - 1;
    }
}

method RotateLeftAlex(a: array) // Author: Alex
    requires a.Length > 0
    modifies a
    ensures forall i::(0 <= i < a.Length -1 ) ==> (a[i] == old(a[(i + 1) % a.Length]))
    ensures a[a.Length -1] == old(a[0])
{
    var n := 0;

    while (n != a.Length - 1)
        invariant 0 <= n <= a.Length -1
        invariant forall i:: (0 <= i < n) ==> (a[i]) == old(a[i+1])
        invariant a[n] == old(a[0])
        invariant forall i :: n < i <= a.Length -1 ==> a[i] == old(a[i])
        {
            a[n], a[n+1] := a[n+1], a[n];
            n := n+1;
        }
}

method RotateLeftTimeOut(a: array) // timeout
    requires a.Length > 0
    modifies a
    ensures forall i::(0 <= i < a.Length -1 ) ==> (a[i] == old(a[(i + 1) % a.Length]))
    ensures a[a.Length -1] == old(a[0])
{
    var n := 0;

    while (n != a.Length - 1)
        invariant 0 <= n <= a.Length -1
        invariant forall i:: (0 <= i < n) ==> (a[i]) == old(a[i+1])
        invariant a[n] == old(a[0])
        invariant forall i :: n < i <= a.Length -1  ==> a[i] == old(a[i])
        {
            assert a[n+1] == old(a[n+1]);
            a[n], a[n+1] := a[n+1], a[n];
            assert a[n] == old(a[n+1]);
            n := n+1;
        }
}