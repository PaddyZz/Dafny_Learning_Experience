ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

method ComputeCount(ORIGindex: nat,CountIndex:nat,CountValue:nat, a:seq<int>, b:array<int>) 
    requires 0 <= CountIndex < b.Length && 0 <= ORIGindex < b.Length && b.Length > 0  && |a| == b.Length
    modifies b 
    decreases CountIndex, |a| - CountValue
    //ensures  a[ORIGindex] % 2 == 0 && ORIGindex != 0 ==> b[ORIGindex] == Count(ORIGindex, a)
{
    
    if CountIndex == 0 {
        if a[CountIndex] % 2 == 0 {
            b[ORIGindex] := CountValue + 1;
        }
        else {
            b[ORIGindex] := CountValue;
        }
    }
    else {
        if a[CountIndex] % 2 == 0{
            ComputeCount(ORIGindex,CountIndex -1, CountValue + 1, a,b);
        }
        else{
            ComputeCount(ORIGindex,CountIndex -1, CountValue, a, b);
        }
    }
}

method PreCompute(a:array<int>, b:array<int>)
    requires a.Length == b.Length && b.Length > 0
    modifies b
    ensures forall i:: 0 <= i < a.Length ==>  b[i] == Count(i, old(a[..]))
   
    
{
     var n := 0;
     while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i:: 0<= i < n ==> b[i] == Count(i, old(a[..]))
        invariant forall i:: n <= i < a.Length ==> b[i] == old(b[i])
        invariant n == 0 && a[n] % 2 == 0 ==> b[n] == Count(n,old(a[..]))+1
        invariant 0 < n <a.Length && a[n] % 2 == 0 ==> b[n] ==  Count(n,old(a[..])) + 1
        
     {
        ComputeCount(n,n,0,a[..],b);
        n := n + 1;
     }
}    


   
    