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

import "elliptic_curve.m": TraceOfFrobeniusWithLI;

function EulerFactorWithLI_(E, X, LIs, v, D, P);
  R<T> := PolynomialRing(ImageRing(X));
  q := ResidueOrder(X);
  if P lt D then
    return R ! 1;
  end if;
  T_D := T ^ D;
  if P lt 2 * D then
    return 1 - TraceOfFrobeniusWithLI(E, LIs, v) * X(v) * T_D;
  end if;
  K<t> := BaseRing(E);
  k<a> := BaseRing(K);
  for LI in LIs do
    if K ! v eq Minimum(LI[1]) then
      return 1 - TraceOfFrobeniusWithLI(E, LIs, v) * X(v) * T_D;
    end if;
  end for;
  return 1 - TraceOfFrobeniusWithLI(E, LIs, v) * X(v) * T_D
    + q ^ D * X(v) ^ 2 * T_D ^ 2;
end function;

intrinsic EulerFactor(E :: CrvEll[FldFunRat[FldFin]], X :: GrpDrchFFElt,
    v :: Any : Exponent := 1, Precision := Infinity()) -> RngUPolElt
{ The Euler factor L_v(E, X, T^D) of an elliptic curve E over k(t) twisted by a
  Dirichlet character at a place v of k(t), which must either be a prime element
  of k[t] or 1 / t, where D is some Exponent. If Precision is set to be finite,
  then this is truncated to a polynomial of degree at most Precision. By
  default, Exponent is set to be 1 and Precision is set to be infinity. }
  K<t> := BaseField(X);
  require IsCoercible(K, v): "The place v is not an element of k(t).";
  v := K ! v;
  require Denominator(v) eq 1 or v eq 1 / t:
    "The place v is neither an element of k[t] nor 1 / t.";
  requirege Exponent, 0;
  return EulerFactorWithLI_(E, X, LocalInformation(E), v, Exponent, Precision);
end intrinsic;

intrinsic EulerFactor(E :: CrvEll[FldFunRat[FldFin]], X :: GrpDrchFFElt :
    Exponent := 1, Precision := Infinity()) -> RngUPolElt
{ The Euler factor L_v(E, X, T^D) of an elliptic curve E over k(t) twisted by a
  Dirichlet character at v = 1 / t, where D is some Exponent. If Precision is
  set to be finite, then this is truncated to a polynomial of degree at most
  Precision. By default, Exponent is set to be 1 and Precision is set to be
  infinity. }
  return EulerFactor(E, X, 1 / Variable(X) : Exponent := 1,
      Precision := Precision);
end intrinsic;