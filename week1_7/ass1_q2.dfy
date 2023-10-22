method DivMod(a: int, b: int) returns (q: int, r: int)
 requires a >= 0 && b > 0
 ensures a == q*b + r && 0 <= r < b
{   
    {a >= 0}
    { true && true && a >= 0} ((k is of type nat))
    {0 >= 0 && b == 1*b && a >= 0} (Definition of Power)
    var c := b;
    {0 >= 0 && c == Power(0)*b && a >= 0} 
    var k := 0;
    {k >= 0 && c == Power(k)*b && a >= 0}
    while c <= a
        invariant k >= 0 && c == Power(k)*b && a >= 0
    {   
        {c <= a && k >= 0 && c == Power(k)*b && a >= 0} (strengthening)
        {k >=0 && 2*c == Power(k+1)*b && a >= 0 } (strengthening)
        {k >= -1 && 2*c == Power(k+1)*b && a >= 0 }
        {k+1 >= 0 && 2*c == Power(k+1)*b && a >= 0}
        c, k := 2*c, k + 1;
        {k >= 0 && c == Power(k)*b && a >= 0}
    }
    {k >=0 && c == Power(k)*b &&  0 <= a < c}
    {k >=0 && c == Power(k)*b && true && 0 <= a < c}
    {k >=0 && c == Power(k)*b && a == a && 0 <= a < c}
    q, r := 0, a;
    {k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c}
    while c != b
        invariant k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c
    {       
            {
                c!= b && k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c
            } (strengthening)
            {
                ( k -1 >= 0 && c/2 == Power(k-1)*b && a == (q+1)*2*c/2 + (r-c/2) && c/2 <= r < c)
                || ( k-1 >= 0 && c/2 == Power(k-1)*b && a == q*2*c + r && 0 <= r < c/2 )
            } (A.1)
            {
               (r >= c/2 &&  k -1 >= 0 && c/2 == Power(k-1)*b && a == (q+1)*2*c/2 + (r-c/2) && c/2 <= r < (2*c)/2)
               || (r < c/2 && k-1 >= 0 && c/2 == Power(k-1)*b && a == q*2*c + r && 0 <= r < c/2 ) 
            } (A.38)

            {(r >= c/2 ==>  k -1 >= 0 && c/2 == Power(k-1)*b && a == (q+1)*2*c/2 + (r-c/2) && c/2 <= r < (2*c)/2
            )&& (r < c/2 ==> k-1 >= 0 && c/2 == Power(k-1)*b && a == q*2*c + r && 0 <= r < c/2 )}
            q, c, k := q*2, c/2, k - 1;
            {(r >= c ==>  k >= 0 && c == Power(k)*b && a == (q+1)*c + (r-c) && c <= r < 2*c
            )&& (r < c ==> k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c)}
            if r >= c {
                { k >= 0 && c == Power(k)*b && a == (q+1)*c + (r-c) && c <= r < 2c}
                { k >= 0 && c == Power(k)*b && a == (q+1)*c + (r-c) && 0 <= (r-c) < c}
                q, r := q + 1, r - c;
                {k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c}
            }
            {k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c}
    }
    {c == b && k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c} (strengthening)
    {a == q*b + r && 0 <= r < b}
}