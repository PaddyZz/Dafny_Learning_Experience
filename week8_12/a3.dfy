class TwoStacks<T(0)(==)> 
{
    //abstract state
    ghost var s1 :seq<T>
    ghost var s2 :seq<T>
    ghost const N :nat // maximum size of the stacks
    ghost var Repr : set<object>
    //concrete state
    var data: array<T>
    var n1: nat // number of elements in the stack 1
    var n2: nat // number of elements in the stack 2
    var wr1: nat // index of the element to be push in the stack 1
    var rd1: nat // index of the element to be pop in the stack 1
    var wr2: nat // index of the element to be push in the stack 2
    var rd2: nat // index of the element to be pop in the stack 2

    ghost predicate Valid()
        reads this,Repr
        ensures Valid() ==> this in Repr &&  |s1| + |s2| <= N
    {
        this in Repr && data in Repr && data.Length == N  
       // &&  rd1 <=wr1 <= wr2 <= rd2 <= N-1 
         && |s1| + |s2| <= N //&& |s1| <= N && |s2| <= N
        &&  (forall i:: 0<= i < |s1| ==> s1[i] == data[i]) 
        && (forall i:: 0<= i < |s2| ==> s2[i] == data[N-1-i])
       && n1 == |s1| && n2 == |s2|
    }

    constructor (N: nat)
        requires N > 0
        ensures Valid() && fresh(Repr)
        ensures s1 == s2 == [] && this.N == N
    {
        s1,s2,this.N := [],[],N;
        data := new T[N];
        n1, n2, rd1, wr1, rd2, wr2 := 0, 0, 0, 0, N-1, N-1;
        Repr := {this, data};
    }
    
    method push4(element:T) returns (FullStatus:bool)
        requires Valid()
        requires |s1| + |s2| <= N
        modifies Repr
        ensures |s1| + |s2| != N ==> s1 ==  old(s1) + [element];
        ensures Valid() && fresh(Repr - old(Repr))
    {   
        if n1 + n2 == data.Length
        {   
            FullStatus := false;
        }else {
            s1 := old(s1) + [element] ;
            data[n1] := element;
            n1 := n1 +1;
            FullStatus := true;
        }
    } 

    method push3(element:T) returns (FullStatus:bool)
        requires Valid()
        requires |s1| + |s2| != N
        modifies Repr
        ensures s1 ==  old(s1) + [element];
        ensures Valid() && fresh(Repr - old(Repr))
    {   
    
        s1 := old(s1) + [element] ;
        data[n1] := element;
        rd2 := wr2;
        n1 := n1 +1;
        if wr2 == wr1
        {   
            FullStatus := false;
        }else {
            wr1 := wr1 + 1;
            FullStatus := true;
        }
    } 

    method push1(element:T) returns (FullStatus:bool)
        requires Valid()
        requires |s1| + |s2| != N
        requires 0 <= |s1| < N
        requires wr1 <= |s1| -1
        requires (forall i:: 0 <= i < |s1| ==> s1[i] == data[i])
        requires s1[wr1] == element
        modifies Repr
        ensures s1 == old(s1) + [element];
        ensures Valid() && fresh(Repr - old(Repr))
    {   
        assert  forall i:: 0 <= i < |s1| ==> s1[i] == data[i];
        
        assert  s1[wr1] == data[wr1];
        assert  old(s1[wr1]) == data[wr1];
        assert  forall i:: 0 <= i < |s1| ==> s1[i] == data[i];
        assert s1[wr1] == old(s1[wr1]);
        s1 := old(s1) + [element];
        assert s1[wr1] == element;
        assert data[wr1] == element;
        assert s1[wr1] == data[wr1];
        assert  forall i:: 0 <= i < old(|s1|) ==> old(s1[i]) == old(data[i]);
        assert  forall i:: 0 <= i < |s1| ==> s1[i] == data[i];
        data[wr1] := element;
        assert  s1[wr1] == data[wr1];
        assert  s1[|s1| -1] == data[|s1| -1];
        assert  s1[0] == data[0];
        assert  forall i:: 0 <= i < |s1| ==> s1[i] == data[i];
        rd1 := wr1;
        assert  forall i:: 0 <= i < |s1| ==> s1[i] == data[i];
        
       // s1 := old(s1) + [element];
        //data[wr1] := element;
       // rd1 := wr1;
        if wr1 == wr2
        {
            FullStatus := false;
        }else {
            wr1 := wr1 + 1;
            FullStatus := true;
            
        }
    } 

    method push2(element:T) returns (FullStatus:bool)
        requires Valid()
        requires |s1| + |s2| != N
        modifies Repr
        ensures s2 == [element] + old(s2) ;
        ensures Valid() && fresh(Repr - old(Repr))
    {   
    
        s2 := [element] + old(s2);
        data[wr2] := element;
        rd2 := wr2;
        if wr2 == wr1
        {
            FullStatus := false;
        }else {
            wr2 := wr2 - 1;
            FullStatus := true;
        }
    } 


    method pop1() returns (EmptyStatus:bool, PopedItem:T)
        requires Valid()
        requires rd1 <= |s1|
        modifies Repr
        ensures s1 == old(s1[0..rd1]) 
        ensures Valid() && fresh(Repr - old(Repr))
    {
        s1 := old(s1[0..rd1]);
       // PopedItem := data[rd1];
    }
}