function mult(a:int, b:int):int {
    a*b
}

method Mult(a:int, b:int) returns (x:int) 
    requires a >= 0 && b >= 0 
    ensures x == mult(a, b)
{
    if a == 0 { 
	x := 0;
    } else {
        var y := Mult(a - 1, b); 
        assert y == a*b - b;
        x := y + b;
    }
}