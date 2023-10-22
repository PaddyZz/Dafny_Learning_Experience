method CopyArray(src:array, dst:array)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i:: 0<= i < src.Length ==> dst[i] == old(src[i])
{
    var n:=0;
    while n!= src.Length
        invariant 0 <= n <= src.Length
        invariant forall i:: 0<= i < n ==> dst[i] == old(src[i])
        invariant forall i:: n <= i < src.Length ==> src[i] == old(src[i])
    {
        assert src[n] == old(src[n]);
        dst[n] := src[n];
        assert dst[n] == old(src[n]);
        assert forall i:: 0<= i < n ==> dst[i] == old(src[i]);
        assert forall i:: 0<= i < n+1 ==> dst[i] == old(src[i]);
        n := n+1;
        assert forall i:: 0<= i < n ==> dst[i] == old(src[i]);
    }
}