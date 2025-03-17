/***
MOTIVIC L-FUNCTIONS OVER GLOBAL FUNCTION FIELDS

Let M be a motive with coefficients in the global function field K of a smooth
proper geometrically irreducible curve of genus g over a finite field of order
q. For a prime l not dividing q, its l-adic realisation M_l defines a univariate
power series over Q_l-bar called its formal L-function L(M, T), which is defined
to be the formal product of the reciprocals of L_v(M, T^{deg v}) over all the
places v of K. Here, the local Euler factor L_v(M, T) is a univariate polynomial
over Q_l-bar, defined to be the inverse characteristic polynomial of the choice
of a geometric Frobenius acting on the inertia subrepresentation of M_l.

The proof of the Weil conjectures shows that L(M, T) is a univariate rational
function over Q_l-bar satisfying a functional equation. Specifically,
Grothendieck showed that there are univariate polynomials P(M, T) and Q(M, T)
over Q_l-bar such that L(M, T) Q(M, T) = P(M, T) and deg P(M, T) = d(M), where
d(M) is (2 g - 2) dim M_l + deg f(M) + deg Q(M, T) and f(M) is the conductor of
M_l as a Weil divisor, with Q(M, T) = 1 whenever M_l has no geometric Galois
invariants. Furthermore, Deligne showed that L(M, T) satisfies a functional
equation L(M, T) = e(M) q^{deg f(M) w(M)} T^{deg f(M)} L(M*, 1 / q^{2 w(M)} T),
where M* is the dual motive associated to M, w(M) is an integer related to the
weight of M, and e(M) is the global root number of M that depends only on the
reduction behaviour at the places in the support of f(M).

In particular, the data of Q(M, T) and of L_v(M, T) for all places v of K with
deg v <= d(M) completely determines P(M, T), and hence L(M, T). Furthermore,
assuming that L(M*, T) can be expressed in terms of L(M, T) up to some
automorphism of Q_l-bar, then the functional equation expresses the last
d(M) / 2 coefficients of L(M, T) in terms of the first d(M) / 2 coefficients of
L(M, T), so the latter data also suffices to completely determine L(M, T).

This procedure is summarised in the following abstract formalism. Let S be a set
of polynomials L_v(T) over a ring R, stratified with v such that the subset of
polynomials L_v(T) in S with deg L_v(T) <= d is finite for any integer d, and
let L(T) be their infinite product. If there are univariate polynomials P(T) and
Q(T) over R such that L(T) Q(T) = P(T) has some degree D', then L(T) converges
and can be computed from the finite subset of polynomials L_v(T) in S with
deg L_v(T) <= D, where D is D' - deg Q(T). Furthermore, if there is an epsilon
factor E in R, a weight factor W in R, and a dual automorphism G of R such that
L(T) = E T^D L(W / T)^G, then L(T) can also be computed from the smaller finite
subset of polynomials L_v(T) in S with deg L_v(T) <= D / 2.

This file defines some intrinsics that compute the formal L-function of a motive
with coefficients in a global function field under this abstract formalism.
***/

function LPolynomialWithoutFE(S, D)
  R<T> := Universe(S);
  D +:= 1;
  L := 1;
  for L_v in S do
    L := L * L_v mod T ^ D;
  end for;
  return R ! Coefficients(1 / PowerSeriesRing(BaseRing(R), D) ! L);
end function;

function LPolynomialWithFE(S, D, E, W, G)
  D_2 := Floor(D / 2);
  L := LPolynomialWithoutFE(S, D_2);
  coefficients := Coefficients(L);
  for d := #coefficients to D_2 do
    coefficients[d + 1] := 0;
  end for;
  R<T> := Parent(L);
  W_d := 1;
  for d := D to D_2 + 1 by -1 do
    coefficients[d + 1] := R ! (E * G(coefficients[D - d + 1] * W_d));
    W_d *:= W;
  end for;
  return R ! coefficients;
end function;

intrinsic LPolynomial(S :: {[RngUPolElt]}, D :: RngIntElt :
    FunctionalEquation := false, EpsilonFactor, WeightFactor, DualAutomorphism)
  -> RngUPolElt
{ The product L(T) of a set S of polynomials L_v(T) over a ring R, stratified
  with v such that the subset of polynomials L_v(T) in S with deg L_v(T) <= d is
  finite for any integer d, assuming that it is a univariate polynomial over R
  of degree D. If the FunctionalEquation L(T) = E T^D L(W / T)^G is true, where
  E is the EpsilonFactor, W is the WeightFactor, and G is the DualAutomorphism
  G, then the necessary computation is decreased significantly. By default,
  FunctionalEquation is set to be false, and other arguments are not assigned. }
  requirege D, 0;
  return FunctionalEquation select LPolynomialWithFE(S, D, EpsilonFactor,
      WeightFactor, DualAutomorphism) else LPolynomialWithoutFE(S, D);
end intrinsic;

intrinsic LFunction(S :: {[RngUPolElt]}, D :: RngIntElt : LDenominator := 1,
    FunctionalEquation := false, EpsilonFactor, WeightFactor, DualAutomorphism)
  -> RngUPolElt
{ The product L(T) of a set S of polynomials L_v(T) over a ring R, stratified
  with v such that the subset of polynomials L_v(T) in S with deg L_v(T) <= d is
  finite for any integer d, assuming that there are univariate polynomials P(T)
  and LDenominator Q(T) over R such that L(T) Q(T) = P(T) has degree D. If the
  FunctionalEquation L(T) = E T^D' L(W / T)^G is true, where D' is D - deg Q(T),
  E is the EpsilonFactor, W is the WeightFactor, and G is the DualAutomorphism
  G, then the necessary computation is decreased significantly. By default,
  LDenominator is set to be 1, FunctionalEquation is set to be false, and other
  arguments are not assigned. }
  return LPolynomial(Append(S, LDenominator), D :
      FunctionalEquation := FunctionalEquation, EpsilonFactor := EpsilonFactor,
      WeightFactor := WeightFactor, DualAutomorphism := DualAutomorphism)
    / LDenominator;
end intrinsic;