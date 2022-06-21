load "dupeq.m";

function randomLinearPermutation(FF)
	n := Degree(FF);
	B := Basis(FF);
	I := [];
	span := { FF ! 0 };
	for i in [1..#B] do
		v := Random({ x : x in FF } diff span);
		Append(~I,v);
		span := span join { c1*s + c2*v : c1,c2 in GF(p), s in span } where p is Characteristic(FF);
	end for;

	FROM := [ ];
	TO := [ ];
	for cs in CartesianPower({ x : x in GF(Characteristic(FF)) }, n) do
		inp := &+ [ cs[i] * B[i] : i in [1..n] ];
		out := &+ [ cs[i] * I[i] : i in [1..n] ];
		Append(~FROM,inp);
		Append(~TO,out);
	end for;
	return Interpolation(FROM,TO);
end function;

n := 6;

FF<a> := GF(3^n);
P<y> := PolynomialRing(FF);
Q<x> := quo<P|ideal<P|y^(3^n)-y>>;

F := x^2;
L1 := Q ! randomLinearPermutation(FF);
L2 := Q ! randomLinearPermutation(FF);
G := Evaluate(L1, Evaluate(F,L2));
time tf, l1, l2 := dupeq(F, G : monomial := true);
assert tf eq true;
assert Evaluate(Q ! l1, Evaluate(F, Q ! l2)) eq G;
