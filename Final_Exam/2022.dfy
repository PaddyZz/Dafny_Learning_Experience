method MatchItems(a:array<int>,b:array<int>) returns (c:array<bool>)
    requires a.Length == b.Length
    requires a!=b
    ensures fresh(c) && c.Length == a.Length
    ensures forall i::  0 <= i < a.Length ==> c[i] == true==> a[i] == b[i] 
    ensures forall i::  0 <= i < a.Length ==> a[i] != b[i] ==>c[i] == false
{
    c:= new bool[a.Length];
    var count := 0;
    while count != a.Length
        invariant 0 <= count <= a.Length
        decreases a.Length -count
        invariant forall i:: 0 <= i < count ==> c[i] == true ==>a[i] == b[i] 
        invariant forall i:: 0<= i< count ==> a[i] != b[i] ==> c[i] == false
    {
        if a[count] == b[count]
        {
            c[count] := true;
            assert c[count] == true ==> a[count] == b[count];
            assert a[count] == b[count] ==> c[count] == true;
            assert 5 >=4 ==> 5>=0;
            assert 5>=0 ==> 5>=4;
        }else {
            c[count] := false;
        }
        count := count + 1;
    }
}

method RelatedItems(a:array<int>,b:array<int>) returns(c:array<int>)
    requires a.Length == b.Length
    requires a!=b
    requires forall i,j:: 0<= i < j < a.Length ==> a[i] != a[j]
    requires forall i,j:: 0<= i < j < b.Length ==> b[i] != b[j]
    ensures fresh(c) && c.Length == a.Length
    ensures forall i,j :: 0<=i<j < a.Length ==> c[i] == j ==> a[i] == b[j]
    ensures forall k:: 0 <= k < a.Length ==> c[k] == c.Length ==> exists i,j:: 0<= i<j < a.Length && a[i] != b[j]
{
    c := new int[a.Length];
    var count := 0;
    var sign := false;
    while count != a.Length
        invariant 0 <= count <= a.Length
        decreases a.Length - count
        invariant forall i,j :: 0<= i < j < count ==> c[i] == j ==> a[i] == b[j]
        invariant forall i,j :: 0<=i <count <= j <a.Length ==> c[i] == j ==>a[i] == b[j]
        invariant sign == true ==> forall k:: 0<= k < a.Length ==> c[k] == a.Length ==> exists i,j:: 0<= i<j < a.Length  && a[i] != b[j]
       // invariant forall k:: 0<=k<a.Length ==>c[k] != a.Length && sign == false
    {
        var countSec := 0;
        sign := false;
        while countSec != a.Length 
            invariant 0 <= count < countSec <= a.Length
            decreases a.Length - countSec
            invariant forall i,j :: 0<=i <count <= j <countSec ==> c[i] == j ==>a[i] == b[j]
            invariant forall j:: count <= j<countSec < a.Length ==> c[count] == j ==> a[count] == b[j]
            invariant forall k:: 0<= k < a.Length ==> c[k] == a.Length && sign == true ==> exists i,j:: 0<= i<j < a.Length  && a[i] != b[j]
        {
            assert forall k:: 0 <= k < a.Length ==> c[k] == c.Length ==> exists i,j:: 0<= i<j < a.Length && a[i] != b[j];
            if a[count] == b[countSec] 
            {   
                sign := true;
                c[count] := countSec;
                assert forall k:: 0 <= k < a.Length ==> c[k] == c.Length ==> exists i,j:: 0<= i<j < a.Length && a[i] != b[j];
            }
            countSec := countSec + 1;
            assert forall k:: 0 <= k < a.Length ==> c[k] == c.Length ==> exists i,j:: 0<= i<j < a.Length && a[i] != b[j];
        }
        assert forall k:: 0 <= k < a.Length ==> c[k] == c.Length ==> exists i,j:: 0<= i<j < a.Length && a[i] != b[j];
        if !sign
        {
            c[count] := c.Length;
            assert forall k:: 0 <= k < a.Length ==> c[k] == c.Length ==> exists i,j:: 0<= i<j < a.Length && a[i] != b[j];
            
        }
        assert forall k:: 0 <= k < a.Length ==> c[k] == c.Length ==> exists i,j:: 0<= i<j < a.Length && a[i] != b[j];
        count := count + 1;
    }
}

method NumSearch(P: int -> bool, N: int) returns (r: int)
    requires exists i :: 0 <= i <= N && P(i)
    ensures 0 <= r <= N && P(r)
{
    assert true && exists i:: 0<=i<=N && P(i);
    assert 0 <= 0 <= N <= N && exists i:: 0 <=i <= N && P(i);
    var a, b := 0, N;
  //  var abc := new bool[1];
    assert 0 <= a <= b <= N && exists i :: a <= i <= b && P(i);
    while a != b
        invariant 0 <= a <= b <= N
        invariant exists i :: a <= i <= b && P(i)
        decreases b -a,b
    {
        assert a!=b && 0 <= a <= b <= N && exists i :: a <= i <= b && P(i);
        assert a != b && (!P(a) ==>0 <= a < b <= N && exists i :: a < i <= b && P(i)) &&
        (P(a) ==>0 <= a <= b <= N + 1 && exists i :: a <= i < b && P(i));
        assert (!P(a) ==>0 <= a < b <= N && exists i :: a < i <= b && P(i)) &&
        (P(a) ==>0 <= a <= b <= N + 1 && exists i :: a <= i < b && P(i));
        if !P(a) {
            assert 0 <= a < b <= N && exists i :: a < i <= b && P(i);
            assert 0 <= a+ 1 <= b <= N && exists i :: a+1 <= i <= b && P(i);
            a := a + 1;
            assert 0 <= a <= b <= N && exists i :: a <= i <= b && P(i);
        } else {
            assert 0 <= a <= b <= N + 1 && exists i :: a <= i < b && P(i);
            assert 0 <= a <= b-1 <= N && exists i :: a <= i <= b-1 && P(i);
            b := b - 1;
           assert 0 <= a <= b <= N && exists i :: a <= i <= b && P(i); 
        }
        
        assert 0 <= a <= b <= N && exists i :: a <= i <= b && P(i);
    }
    assert 0 <= a <= b <= N && exists i :: a <= i <= b && P(i) && a == b;
    r := a;
    assert 0 <= a <= b <= N && exists i :: a <= i <= b && P(i) && a == b;
}

method LargestIndex(a: array<int>) returns (r: int)
    requires exists i :: 0 <= i < a.Length && a[i]== i
    ensures 0 <= r < a.Length
    ensures a[r] == r && (forall i :: 0 <= i < a.Length && a[i] == i ==> i <= r)
{
    var count := 1;
    r := 0;
    while count != a.Length
        invariant r < count
        invariant 0 <= count <= a.Length
        decreases a.Length - count
        invariant forall i:: 0<= i < r && a[i] == i ==> i < r
        invariant forall i:: 0<= i< count && a[i] == i ==> a[i] <= a[r] 
        invariant exists r::0 <= r < a.Length&&  a[r] ==r && (forall i:: 0<= i<count ==> i<= r)
       //invariant forall i:: 0<= i< count && a[i] == i ==> i <= r
      //  invariant forall i:: 0<= i <a.Length ==> a[i] == i

    {
        if a[count] >= a[r]
        {
            r:= count;
        }
        count := count + 1;
    }
}

class Item {
    var id: int
    var quantity: int
    constructor(id: int, quantity: int)
    function  GetId(): int
    function GetQuantity(): int
}

class Inventory {
    ghost var data : seq<Item> // the items in the inventory 
    ghost var N : int // the (max) number of item in the inventory
    ghost var Repr: set<object> // the set of objects implementing in the inventory
    var contents: array?<Item?>
    var numItems: int
    //method Add(item: Item)
   // function GetQuantity(id: int): int

    ghost predicate Valid()
        reads this, Repr
        ensures Valid() ==> this in Repr
    {
        this in Repr 
        && contents in Repr && numItems == |data| 
        && contents.Length == N
        && |data| <= N
        && data == contents[..numItems]
        && forall i:: numItems <= i < N ==> contents[i] == null
        && forall i:: 0 <= i < numItems ==> contents[i] != null
    }

    method Add(item:Item)
        requires Valid()
        requires item.GetQuantity() > 0
        modifies Repr
        ensures data == old(data) + [item]
        ensures N == old(N)
        ensures Valid() && fresh(Repr-old(Repr))
/*
    function GetQuantity(id:int):int
        reads Repr
        ensures GetQuantity == 
    
    function SubGetQuantity(id:int,ItemNums:int):int
        requires 0 <= ItemNums <= this.numItems
        reads Repr
    {
        if ItemNums == 0 then 0
        else if contents[ItemNums-1] == id then 1 + SubGetQuantity(id,ItemNums -1) else SubGetQuantity(id,ItemNums-1)
    }*/
}

method NumSearchOne(P: int -> bool, N: int) returns (r: int)
    requires exists i :: 0 <= i <= N && P(i)
    ensures 0 <= r <= N && P(r)
{
    var a, b := 0, N;
    while a != b
        invariant 0 <= a <= b <= N
        invariant exists i :: a <= i <= b && P(i)
    {

        assert (!P(a) ==>exists i :: a+1 <= i <= b && P(i) && 0 <= a+1 <= b <= N) &&
         (P(a) ==> exists i :: a <= i <= b-1 && P(i) && 0 <= a <= b-1 <= N) && a!=b;
        assert (!P(a) ==>exists i :: a+1 <= i <= b && P(i) && 0 <= a+1 <= b <= N) &&
         (P(a) ==> exists i :: a <= i <= b-1 && P(i) && 0 <= a <= b-1 <= N);
        if !P(a) {
            assert exists i :: a+1 <= i <= b && P(i) && 0 <= a+1 <= b <= N;
            a := a + 1;
            assert exists i :: a <= i <= b && P(i) && 0 <= a <= b <= N;
        } else {
            assert exists i :: a <= i <= b-1 && P(i) && 0 <= a <= b-1 <= N;
            b := b - 1;
            assert exists i :: a <= i <= b && P(i) && 0 <= a <= b <= N;
        }
        assert exists i :: a <= i <= b && P(i) && 0 <= a <= b <= N;
    }
    assert 0<= a <= N && P(a) && a ==b;
    r := a;
    assert 0 <= r <= N && P(r);
}

method A(x:int,y:int,n:int)returns (r:int)
    requires n>0 && x>=0 && y>= 0
    ensures 0 <= r <= n
{
    assert (x+y <n ==> 0<=n-y <=n) && (x+y>=n ==>x>=0 && y>=0 && n>0);
    if x+y <n{
        assert 0<= n-y<=n;
        r:= n -y;
        assert 0 <= r <= n;
    }else{
        assert x>=0 && y>=0 && n>0 && true;
        assert x>=0 && y>=0 && n>0 && 0<= n-(x+y)%n<= n;
        assert x>=0 && y>=0 && n>0 &&  forall r':: r'==(x+y)%n ==> 0<= n-r'<= n; // one-point rule
        r:= B(x,y,n);
        assert 0<= n-r <=n;
        r:=n-r;
        assert 0 <= r <= n;
    }
}

method B(x:int,y:int,n:int) returns (r:int)
    requires n>0 && x>=0 && y>=0
    ensures r ==(x+y)%n

method C(n:int) returns (r:int)
    requires n>=2
    ensures r <= n && forall j::2<=j<r ==> n%j !=0
{
    var i:=2;
    while n % i != 0
        invariant 2<= i <= n 
        decreases n-i
        invariant forall j::2<=j<i ==> n%j !=0
       // invariant r <= n || (forall j::2<=j<i ==> n%j ==0)
    {
        i:=i+1;
    }
    assert i <= n;
    assert n %i == 0;
    assert forall j::2<=j<i ==> n%j !=0;
    r:=i;
}