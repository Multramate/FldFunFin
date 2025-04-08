/*
L-FUNCTIONS OF DIRICHLET TWISTS OF ELLIPTIC CURVES OVER GLOBAL FUNCTION FIELDS

Let E be an elliptic curve over a global function field K of a smooth proper
geometrically irreducible curve of genus g over a finite field k of order q, and
let X be a Dirichlet character over K, with modulus a non-zero element M of
k[t]. Assume that the conductors of E and X have disjoint support, and assume
for now that M is irreducible.

The twist E x X of E by X is the tensor product motive h^1(E)(1) x [X] with
w(E x X) = 1, whose l-adic realisation is simply the tensor product H_l(E) x X,
which has no geometric Galois invariants when either E or X has non-trivial
conductor. In this case, the local Euler factor L_v(E, X, T) of E x X at a place
v of K is given by 1 - a_v(E) X(v) T + q_v X(v)^2 T^2 if E has good reduction at
v, and 1 - a_v(E) X(v) T otherwise. The formal L-function L(E, X, T) is then a
polynomial of degree d(E x X) equal to 2d(X) + d(E) - 4.

This file defines some intrinsics that compute the formal L-function of an
elliptic curve twisted by a Dirichlet character of irreducible moduli over the
global function field k(t) of the projective line over k, which has a unique
place at infinity 1 / t.
*/