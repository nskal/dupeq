function listPlanar3()
	FF<a> := GF(3^3);
	P<x> := PolynomialRing(FF);
	Fs := [
		x^2,
		x^4
	];
	return Fs;
end function;

function listPlanar4()
	FF<a> := GF(3^4);
	P<x> := PolynomialRing(FF);
	Fs := [
		x^2,
		x^14,
		x^36 + 2*x^10 + 2*x^4
	];
	return Fs;
end function;

function listPlanar5()
	FF<a> := GF(3^5);
	P<x> := PolynomialRing(FF);
	Fs := [
		x^2,
		x^4,
		x^10,
		x^10 + x^6 + 2*x^2,
		x^10 + 2*x^6 + 2*x^2,
		x^14,
		x^90 + x^2,
		x^162 + x^108 - x^84 + x^2
	];
	return Fs;
end function;

function listPlanar6()
	FF<a> := GF(3^6);
	P<x> := PolynomialRing(FF);
	Fs := [
		x^2,
		x^10,
		x^162 + x^84 + a^58*x^54 + a^58*x^28 + x^6 + a^531*x^2,
		a^75*x^2214 + x^756 + a^205*x^82 + x^28,
		2*x^270 + x^246 + 2*x^90 + x^82 + x^54 + 2*x^30 + x^10 + x^2,
		x^270 + 2*x^244 + a^449*x^162 + a^449*x^84 + a^534*x^54 + 2*x^36 + a^534*x^28 + x^10 + a^449*x^6 + a^279*x^2,
		x^486 + x^252 + a^561*x^162 + a^561*x^84 + a^183*x^54 + a^183*x^28 + x^18 + a^561*x^6 + a^209*x^2,
		x^122,
		a^438*x^486 + a^180*x^324 + a^458*x^270 + a^672*x^252 + a^622*x^246 + a^94*x^244 + a^650*x^162 + a^441*x^108 + a^50*x^90 + x^84 + a^77*x^82 + a^328*x^36 + a^583*x^30 + a^407*x^28 + a^178*x^18 + a^492*x^12 + a^692*x^10 + a^78*x^6 + a^219*x^4 + a^69*x^2,
		a^91*x^30 + x^10 + x^2,
		a^91*x^486 + x^10 + x^2,
		a^182*x^82 + 2*x^10 + a^91*x^6 + x^2,
		a^182*x^82 + 2*x^10 + a^273*x^6 + x^2,
		a^91*x^486 + a^182*x^90 + 2*x^10 + x^2,
		a^273*x^486 + a^182*x^90 + 2*x^10 + x^2,
		a^273*x^246 + a^182*x^82 + a^91*x^6 + x^2
	];
	return Fs;
end function;

function listPlanar7()
	FF<a> := GF(3^7);
	P<x> := PolynomialRing(FF);
	Fs := [
		x^2,
		x^4,
		x^10,
		x^28,
		x^10 + x^6 + 2*x^2,
		x^10 + 2*x^6 + 2*x^2,
		x^14,
		x^122
	];
	return Fs;
end function;

function listPlanar8()
	FF<a> := GF(3^8);
	P<x> := PolynomialRing(FF);
	Fs := [
		x^2,
		x^14,
		x^122,
		x^1094,
		a^3994*x^244 + a^5354*x^84 + 2*x^82,
		a^264*x^1458 + x^82,
		a^3698*x^2188 + a^1058*x^108 + 2*x^82,
		x^4374 + x^2430 + x^2214 + 2*x^2190 + 2*x^1458 + 2*x^810 + x^486 + 2*x^270 + x^246 + x^82 + x^54 + x^30 + x^18 + x^10 + x^6 + x^2,
		a^3608*x^1458 + a^3608*x^738 + a^3810*x^486 + a^3810*x^246 + a^3413*x^162 + a^3413*x^82 + a^3608*x^18 + a^3810*x^6 + a^2565*x^2,
		a^164*x^1458 + a^164*x^738 + a^950*x^486 + a^950*x^246 + a^616*x^162 + a^616*x^82 + a^164*x^18 + a^950*x^6 + a^6297*x^2
	];
	return Fs;
end function;
