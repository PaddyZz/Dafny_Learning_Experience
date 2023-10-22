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
         && |s1| + |s2| <= N && 0 <=|s1| <= N && 0 <=|s2| <= N
        &&  (forall i:: 0<= i < |s1| ==> s1[i] == data[i]) 
        && (forall i:: 0<= i < |s2| ==> s2[i] == data[data.Length-1-i])
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
    
    method push1(element:T) returns (FullStatus:bool)
        requires Valid()
        requires |s1| + |s2| <= N
        modifies Repr
        ensures |s1| != N && |s1| + |s2| != N ==> s1 ==  old(s1) + [element];
        ensures Valid() && fresh(Repr - old(Repr))
    {   
        if n1  == data.Length
        {   
            FullStatus := false;
        }else {
            if n1 != data.Length && n1 + n2 != data.Length{
                s1 := old(s1) + [element] ;
                data[n1] := element;
                n1 := n1 +1;
                FullStatus := true;
            }else{
                FullStatus := false;
            }
        }
    } 

    method push2(element:T) returns (FullStatus:bool)
        requires Valid()
        requires |s1| + |s2| <= N
        modifies Repr
        ensures |s1| + |s2| != N ==> s2 == old(s2) + [element] ;
        ensures Valid() && fresh(Repr - old(Repr))
    {   
    
        if n1 + n2 == data.Length
        {   
            FullStatus := false;
        }else {
            s2 := old(s2) + [element];
            data[data.Length - n2 -1] := element;
            n2 := n2 + 1;
            FullStatus := true;
        }
    } 


    method pop1() returns (EmptyStatus:bool, PopedItem:T)
        requires Valid()
        requires |s1| != 0 
        modifies Repr
        ensures s1 == old(s1[0..|s1|-1])
        ensures Valid() && fresh(Repr - old(Repr))
    {
        assert 0 <= old(|s1|) <= N;
        assert 0 <= |s1| <= old(|s1|) <= N;
    

        assert n1 != 0 ==> |old(s1[0..|s1|-1])| != 0 ==> true;
        if n1 != 0 { 
            if n1 == data.Length
            {
                 assert |old(s1[0..|s1|-1])| != 0 ==> true;
                s1 := old(s1[0..|s1|-1]);
                
                PopedItem := data[n1-1];
                n1 := n1 -1;
                EmptyStatus := true;
                 assert |s1| != 0 ==> s1 == old(s1[0..|s1|-1]);
            }else {
                 assert |old(s1[0..|s1|-1])| != 0 ==> true;
                assert n1 != 0 && n1 < data.Length;
                assert |old(s1[0..|s1|-1])| != 0 ==> old(s1[0..|s1|-1]) == old(s1[0..|s1|-1]);
                s1 := old(s1[0..|s1|-1]);
                 assert |s1| != 0 ==> s1 == old(s1[0..|s1|-1]);
                PopedItem := data[n1-1];
                n1 := n1 -1;
                EmptyStatus := true;
                // assert |s1| != 0 ==> s1 == old(s1[0..|s1|-1]);
            }
            assert n1 != 0 ==> s1 == old(s1[0..|s1|-1]);
            assert |s1| != 0 ==> s1 == old(s1[0..|s1|-1]);
        } else{
            if n1 == 0 && n1 + n2 !=0 {
                assert |s1| == 0 ==> EmptyStatus == false;
                EmptyStatus := false;
                PopedItem := *;
                assert |s1| == 0 ==> EmptyStatus == false;
            }else {
                assert n1 == 0 && n1 + n2 == 0;
                assert |s1| == 0 ==> EmptyStatus == false;
                EmptyStatus := false;
                PopedItem := *;
                assert |s1| == 0 ==> EmptyStatus == false;
            }
           assert |s1| == 0 ==> EmptyStatus == false;
        }
        
         assert |s1| != 0 ==> s1 == old(s1[0..|s1|-1]);
    }

    method pop2() returns (EmptyStatus:bool, PopedItem:T)
        requires Valid()
     //   requires |s1| != 0 
        modifies Repr
        ensures |s1| != 0 ==> s1 == old(s1[0..|s1|-1])
        ensures Valid() && fresh(Repr - old(Repr))
    {
 
        if n1 == 0 { 
            s1 := old(s1[0..|s1|]);
            EmptyStatus := false;
            PopedItem := *;

        } else{
            s1 := old(s1[0..|s1|-1]);
            PopedItem := data[n1-1];
            n1 := n1 -1;
            EmptyStatus := true;
        }
    }
}