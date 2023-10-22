 
method D(a: nat, b: nat) 
    decreases a,1,b
   
{
    if b == 0 {
        C(a);
    } else {
        assert a> a-1 && a>=0 &&  b > b-1 && b>=0;
        ghost var d,p := a,b;
        assert d> a-1 && d>=0 &&  p > b-1 && p>=0;
        D(a, b - 1);
        assert d> a-1 && d>=0 &&  p > b-1 &&p>=0;
    }
}

 method C(a: nat) 
    decreases a ,0
 {
    ghost var d:= a;
    if a != 0 {
        var b := a - 1;
        assert a> a-1 && a> 0;
        assert a> a-1 && a>= 0;
        
        assert d> a-1 && d>= 0;
        D(a - 1, b);
        assert d> a-1 && d>= 0;
    }
    
}

/* for method C: decreases: a,0
 for method D: decreases:a,1,b
  on the recursive call from C to D,we have a,0 > a-1 ,1 ,b when a is type of nat and a> a-1  and a>=0 
    on the recursive call from D to D, we have a,1,b> a,1, b-1 when b is the type of nat and b>b-1 and b>=0
    on the recursive call from D to C, we have a,1,b > a, 0 when 1>0 and 1>=0 
/*
method A(x: int) returns (y: int)
    requires x > 0
    ensures y < 10
 {
    assert (x < 8 ==> (x == 5 ==> false && x != 5 ==> true)) && (x >= 8 ==> true)
    if x < 8 {
        assert x == 5 ==> false && x != 5 ==> true;
        if x == 5 {
           // assert false;
            assert 10 < 10;
            y := 10;
            assert y < 10;
        } else {
            assert true;
            assert 2 < 10;
            y := 2;
            assert y < 10;
        }
    } else {
        assert true;
        assert 0 < 10;
        y := 0;
        assert y < 10;
    }
 } */

 method B(x: int, y: int) returns (r: int)
        requires x >= 0 && y >= 0
        ensures r == x * y
    {
        assert (x==0 || (x>0 && y >= 0));
        assert x != 0 ==> x>=0 && y >=0;
        assert true && (x !=0 ==>x >=0 && y >=0);
        assert( x == 0 ==> 0 == x * y) && (x !=0 ==>x >=0 && y >=0);
        if x == 0 {
            assert 0 == x * y;
            r := 0;
            assert  r == x * y;
        } else {
            assert x>=1 && y>=0;
            assert x-1>= 0 && y >= 0;
            assert x >= 0 && y >= 0 && true;
            assert x >= 0 && y >=0 && x*y -y + y == x * y;
            assert x>= 0 && y>= 0 && (x-1)*y + y == x * y;
            assert x >= 0 && y >= 0 && forall r':: r' == (x-1) *y ==> r' + y == x * y;
            var z := B(x - 1, y);
            assert z + y == x * y;
            r := z + y;
            assert  r == x * y;
        }
    }

method BB(x: int, y: int) returns (r: int)
    requires x >= 0 && y >= 0
    ensures r == x * y
    {
        if x == 0 {
            r := 0;
        } else {
            assert x-1 >= 0 && y >= 0 && forall r'::r'==(x-1)*y ==> r' +y == x*y;
            var z := BB(x - 1, y);
            assert z+y == x*y;
            r := z + y;
            assert r == x * y;
        }
        assert r == x * y;
    }

method DoubleArray(a:array<int>) 
    modifies a
    ensures forall i:: 0<= i<a.Length ==> a[i] == 2*old(a[i])
    var n:= 0
    while n != a.Length 
        invariant 0<=n <= a.Length
        invariant forall i::0<= i < n ==> a[i] == 2*old(a[i])
        invariant forall i:: n<= i<a.Length ==> a[i] == old(a[i])
        decreases a.Length - n

*/
function M(x: int, b: bool): int 
    decreases !b
{
 if b then x else M(x + 25, true)
 }

 /* on the recursive call from M to M, we have b > !b when b && !b

 /*g
 abstract state
 ghost var elems:seq<(int,int)>;
 ghost const max: nat;
 ghost var Repr: set<object>;

 //concrete state

 var start: array<int>;
 var finish: array<int>;
 var n:nat;*/

 */
 ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr && |elems| <= max 
{
    this in Repr && start in Repr&& finish in Repr && start.Length == finish.Length == max && |elems| == n 
    && n <= max && start != finish && (forall i:: 0<= i <n ==> start[i] == elems[i].0 && finish[i] == elems[i].1 && start[i] < finish[i]) 
    && (forall i,j:: 0<= i<j <n ==>!(elems[i].0 <= elems[j].0 <= elems[j].1)&& !(elems[i].0 && elems[j].1 && elems[i].1) )
}
method constructor(max:nat)
    ensures Valid() && fresh(Repr)
    ensures elems ==[] && this.max == max
    
method Add(s:int,f:int)
    requires Valid() && s<f && |elems| < max
    requires forall i:: 0 <= i < n ==> !(elems[i].0 <= s<= elems[i].1) && !(elems[i].0 <= f <= elems[i].1)
    modifies Repr
    ensures elems == old(elems) + [(s,f)]
    ensures Valid() && fresh(Repr - old(Repr))

method Cancel(s:int, f:int)
    requires Valid() && exists i :: 0<= i < |elems| && elems[i]== (s,f)
    modifies Repr
    ensures Valid() && fresh(Repr-old(Repr))
    ensures exists s1,s2 :: old(elems) == s1 + [(s,f)]+s2 && elems == s1 + s2

// intrinsic 

ensures Length(Snoc(xs,y)) == Length(xs) +1 
function Reverse<T> (xs:List<T>):List<T>
{
    match xs
    case Nil=> Nil
    case Cons(x,tail) => Snoc(Reverse(xs),x);}
lemma what<T> (xs:List<T>)
    ensures Length(Reverse(xs)== Length (xs))
{}