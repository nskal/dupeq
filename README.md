#Test for linear equivalence of 2-to-1 planar functions in characteristic 3

An implementation of the algorithm described in [Deciding and reconstructing linear equivalence of uniformly distributed functions](https://eprint.iacr.org/2022/666).

This implementation is in the Magma algebra system. The functions being compared must be represented as univariate polynomials over GF(3^n), e.g.

```
FF<a> := GF(3^n);
P<x> := PolynomialRing(FF);
F := x^2;
G := x^6;
```

The following main methods are available:
- `dupeq(F,G)`: compares F and G for linear equivalence without making any further assumptions;
- `dupeq_with_l2_representatives(F,G,O)`: compares F and G for linear equivalence, using the fact that O contains representatives from all right orbits under F;
- `dupeq(F,G : monomial := true)`: a faster implementation in the case when F is a monomial (in essence, this calls dupeq_with_l2_representatives for O = { 1 }).

In order to compute the right orbits of a given function, one can call:
- `partitionByL2(F)`.

A minimal example of usage is provided in `example.m`.
