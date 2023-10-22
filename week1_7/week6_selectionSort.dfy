method selectionSort(a:array <int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var n := 0;
    while n != a.Length
        invariant 0<= n <= a.Length
        invariant forall i,j :: 0<=i <j < n ==> a[i] <= a[j]
        invariant forall i,j :: 0 <= i < n <= j< a.Length ==> a[i] <= a[j]
        
        invariant multiset(a[..]) == old(multiset(a[..]))
        {
            var mindex, m := n, n;
            while m!=a.Length
                invariant 0 <= n <= m <=a.Length
                invariant n <= mindex < a.Length
                invariant forall i:: n<= i< m ==> a[mindex] <= a[i]
                {
                    assert a[m] < a[mindex] ==> forall i:: n<= i< m ==> a[mindex] <= a[i];
                    if a[m] < a[mindex] {
                        assert forall i:: n<= i< m ==> a[m] <= a[i];
                        mindex := m;
                        assert forall i:: n<= i< m ==> a[mindex] <= a[i];
                    }
                    assert forall i:: n<= i< m ==> a[mindex] <= a[i];
                    m := m + 1;
                }

            
            a[mindex], a[n] := a[n],a[mindex];

            
            
            assert forall i:: 0<= i < n ==> a[i] <= a[n];
            assert forall i,j :: 0<=i <j < n ==> a[i] <= a[j];
            assert  forall i,j :: 0<=i <j < n+1 ==> a[i] <= a[j];
            n := n + 1;
            assert forall i,j :: 0<=i <j < n ==> a[i] <= a[j];
        }

}
