while c != b
    invariant k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c
    {   

        {(k -1>=0 && c/2 == Power(k-1)*b && a == q*2*(c/2) + r) && (0 <= r < c)
        }(1b)
        {((r >= c/2 ==> k -1 >=0 && c/2 == Power(k-1)*b && a == q*2*(c/2) + r ) 
        && (r< c/2 ==> k -1 >= 0 && c/2 == Power(k -1)*b && a == q*2*(c/2) + r)) 
        &&(r<c && r >=0)
        }(A.2, A.4)
        {((r >= c/2 ==> k -1 >=0 && c/2 == Power(k-1)*b && a == q*2*(c/2) + r) && (r < c))
         && ((r < c/2 ==> k -1 >= 0 && c/2 == Power(k -1)*b && a == q*2*(c/2) + r ) && (r >= 0))
        }(strengthening)
        {((r >= c/2 ==> k -1 >=0 && c/2 == Power(k-1)*b && a == q*2*(c/2) + r) && (r < c/2 || r < c))
            && ((r < c/2 ==> k -1 >= 0 && c/2 == Power(k -1)*b && a == q*2*(c/2) + r ) && (r >= c/2 || r >= 0))
        }
        {( (r >= c/2 ==> k -1 >=0 && c/2 == Power(k-1)*b && a == q*2*(c/2) + r) && (r >= c/2 ==> r < c))
            && ((r < c/2 ==> k -1 >= 0 && c/2 == Power(k -1)*b && a == q*2*(c/2) + r ) && (r < c/2 ==> 0 <= r ))
        } (A.33)
        { (r >= c/2 ==> k -1 >=0 && c/2 == Power(k-1)*b && a == q*2*(c/2) + r && r < c)
            && (r < c/2 ==> k -1 >= 0 && c/2 == Power(k -1)*b && a == q*2*(c/2) + r && 0 <= r)
        }
        { (r >= c/2 ==> k -1 >=0 && c/2 == Power(k-1)*b && a == q*2*(c/2) + r && r < (2*c)/2)
            && (r < c/2 ==> k -1 >= 0 && c/2 == Power(k -1)*b && a == q*2*(c/2) + r && 0 <= r)
        }
        q, c, k := q*2, c/2, k - 1;
        { (r >= c ==> k>=0 && c== Power(k)*b && a == q*c + r && r < 2*c)
            && (r < c ==> k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r)
        } (1a)
        {(r >= c ==> k>=0 && c== Power(k)*b && a == q*c + r && c <= r  < 2*c)
        && (r < c ==> k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c)}
        if r >= c {
            { k>=0 && c== Power(k)*b && a == q*c + r && c <= r  < 2*c}
            { k>=0 && c== Power(k)*b && a == (q+1)*c + (r-c) && 0 <= r - c < c}
            q, r := q + 1, r - c;
            {k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c}
        }
        {k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c}
    }
    {c == b && k >= 0 && c == Power(k)*b && a == q*c + r && 0 <= r < c } (strengthening)
    {a == q*b + r && 0 <= r < b}