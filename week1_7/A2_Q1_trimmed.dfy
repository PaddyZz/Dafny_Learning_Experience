ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

method ComputeCount(ORIGindex: nat,CountIndex:nat,CountValue:nat, a:seq<int>, b:array<int>) returns (p:nat)
    requires 0 <= CountIndex < b.Length && 0 <= ORIGindex < b.Length && b.Length > 0  && |a| == b.Length
    modifies b 
    decreases CountIndex, |a| - CountValue
    
    
    ensures CountIndex == 0 ==> b[ORIGindex] == CountValue || b[ORIGindex] == CountValue + 1
    ensures CountIndex != 0 ==>( CountIndex == 0 ==>  b[ORIGindex] == CountValue || b[ORIGindex] == CountValue +1 )
{
    p := 0;
    assert CountIndex !=0 ==> CountIndex == 0 ==> b[ORIGindex] == CountValue || b[ORIGindex] == CountValue + 1;
    if CountIndex == 0 {
        if a[CountIndex] % 2 == 0 {
            p := CountValue +1;
            
        }
        else {
            p := CountValue;
        }
        b[ORIGindex] := p;
    }
    //assert CountIndex == 0 ==> b[ORIGindex] == CountValue || b[ORIGindex] == CountValue + 1;
    else {
        assert CountIndex == 0 ==> b[ORIGindex] == CountValue || b[ORIGindex] == CountValue + 1;
        if a[CountIndex] % 2 == 0{
            assert CountIndex == 0 ==> b[ORIGindex] == CountValue || b[ORIGindex] == CountValue + 1;
           p := ComputeCount(ORIGindex,CountIndex -1, CountValue + 1, a,b);
           assert CountIndex == 0 ==> b[ORIGindex] == CountValue || b[ORIGindex] == CountValue + 1;
        }
        else{
            p := ComputeCount(ORIGindex,CountIndex -1, CountValue, a, b);
        }
    }
}

method PreCompute(a:array<int>, b:array<int>)
    requires a.Length == b.Length && b.Length > 0
    modifies b
 
    ensures forall i:: 0 <= i < a.Length ==>  b[i] == Count(i, old(a[..])) || (a[i]%2 == 0 && b[i] == Count(i,old(a[..])) + 1)

{
     var n := 0;
     var CountValue := 0;
     while n != a.Length
       // decreases a.Length - n,a.Length - CountValue
        invariant 0 <= n <= a.Length
        invariant forall i:: 0<= i < n ==> b[i] == Count(i, old(a[..])) || (a[i]%2 == 0 && b[i] == Count(i,old(a[..]))+1)
        //invariant forall i:: n <= i < a.Length ==> b[i] == old(b[i])
        //s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
        invariant 1+ Count(n-1,a[..]) == Count(n,a[..]) ==> a[n-1]% 2== 0 && n >=1
        invariant (n == 0 ==> b[n] == CountValue || b[n] == CountValue + 1) && (n != 0 ==> n == 0 ==> b[n] == CountValue || b[n] == CountValue + 1)
        //invariant n == 0  ==> b[n] == Count(n, old(a[..]))  || ( a[n]%2 == 0 && Count(n, old(a[..])) == 1)       
        invariant n != 0 ==> n == 0 ==> b[n] == CountValue || b[n] == CountValue + 1
     {
        assert (forall i:: 0<= i < n ==> b[i] == Count(i, old(a[..])) || (a[i]%2 == 0 && b[i] == Count(i,old(a[..]))+1))  && (n == 0 ==> b[n] == CountValue || b[n] == CountValue + 1) && (n != 0 ==> n == 0 ==> b[n] == CountValue || b[n] == CountValue + 1);
        assert (n == 0 ==> b[n] == CountValue || b[n] == CountValue + 1) && (n != 0 ==> n == 0 ==> b[n] == CountValue || b[n] == CountValue + 1);
       assert (forall i:: 0<= i < n ==> b[i] == Count(i, old(a[..])) || (a[i]%2 == 0 && b[i] == Count(i,old(a[..]))+1)) ;
       b[n] := ComputeCount(n,n,CountValue,a[..],b);
       assert (forall i:: 0<= i < n ==> b[i] == Count(i, old(a[..])) || (a[i]%2 == 0 && b[i] == Count(i,old(a[..]))+1));
       assert (b[n] == Count(n, old(a[..])) || (a[n]%2 == 0 && b[n] == Count(n,old(a[..]))+ 1));
       assert forall i:: 0<= i < n + 1 ==> b[i] == Count(i, old(a[..])) || (a[i]%2 == 0 && b[i] == Count(i,old(a[..]))+1);
        n := n + 1;
        assert forall i:: 0<= i < n ==> b[i] == Count(i, old(a[..])) || (a[i]%2 == 0 && b[i] == Count(i,old(a[..]))+1);
     }
}    


   
    