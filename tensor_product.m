/* L-FUNCTIONS OF DIRICHLET TWISTED ELLIPTIC CURVES OVER GLOBAL FUNCTION FIELDS

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
place at infinity 1 / t. This includes root numbers and local Euler factors.
*/

import "elliptic_curve.m": ConductorProductWithLI, TraceOfFrobeniusWithLI,
  RootNumberWithLI, LDegreeWithLI;

function RootNumberWithLI_(E, X, LIs)
  return RootNumberWithLI(E, LIs) * RootNumber(X) ^ 2
    * X(ConductorProductWithLI(E, LIs));
end function;

intrinsic RootNumber(E :: CrvEll[FldFunRat[FldFin]], X :: GrpDrchFFElt)
  -> FldCycElt
{ The global root number e(E x X) of an elliptic curve E over k(t) twisted by a
  Dirichlet character X, assuming that the conductors of E and X have disjoint
  support. Note that this has not been implemented for characteristic 2 and 3. }
  K<t> := BaseRing(E);
  require Characteristic(K) gt 3:
    "This has not been implemented for characteristic 2 and 3.";
  return RootNumberWithLI_(E, X, LocalInformation(E));
end intrinsic;

function EulerFactorWithLI_(E, X, LIs, v, D, P);
  R<T> := PolynomialRing(Codomain(X));
  q := ResidueSize(X);
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
  Dirichlet character X at a place v of k(t), which must either be a prime
  element of k[t] or 1 / t, assuming that v is not a bad place for both of E and
  X, where D is some Exponent. If Precision is set to be finite, then this is
  truncated to a polynomial of degree at most Precision. By default, Exponent is
  set to be 1 and Precision is set to be infinity. }
  K<t> := Domain(X);
  require IsCoercible(K, v): "The place v is not an element of k(t).";
  v := K ! v;
  require Denominator(v) eq 1 or v eq 1 / t:
    "The place v is neither an element of k[t] nor 1 / t.";
  requirege Exponent, 0;
  LIs := LocalInformation(E);
  for LI in LIs do
    if K ! v eq Minimum(LI[1]) then
      for M_e in Conductor(X) do
        require v ne M_e[1]: "The place v is bad for both of E and X.";
      end for;
      break LI;
    end if;
  end for;
  return EulerFactorWithLI_(E, X, LIs, v, Exponent, Precision);
end intrinsic;

intrinsic EulerFactor(E :: CrvEll[FldFunRat[FldFin]], X :: GrpDrchFFElt :
    Exponent := 1, Precision := Infinity()) -> RngUPolElt
{ The Euler factor L_v(E, X, T^D) of an elliptic curve E over k(t) twisted by a
  Dirichlet character X at v = 1 / t, assuming that v is not a bad place for
  both of E and X, where D is some Exponent. If Precision is set to be finite,
  then this is truncated to a polynomial of degree at most Precision. By
  default, Exponent is set to be 1 and Precision is set to be infinity. }
  return EulerFactor(E, X, 1 / Domain(X).1 : Exponent := 1,
      Precision := Precision);
end intrinsic;

function EulerFactorsWithLI_(E, X, LIs, D)
  K<t> := Domain(X);
  k<a> := ResidueField(X);
  S := [PolynomialRing(Codomain(X)) | ];
  if D gt 0 then
    Append(~S, EulerFactorWithLI_(E, X, LIs, 1 / t, 1, D));
  end if;
  for i := 1 to D do
    for v in AllIrreduciblePolynomials(k, i) do
      Append(~S, EulerFactorWithLI_(E, X, LIs, K ! v, Degree(v), D));
    end for;
  end for;
  return S;
end function;

intrinsic EulerFactors(E :: CrvEll[FldFunRat[FldFin]], X :: GrpDrchFFElt,
    D :: RngIntElt) -> SeqEnum[RngUPolElt]
{ The finite set of all Euler factors of an elliptic curve E over k(t) twisted
  by a Dirichlet character X, assuming that the conductors of E and X have
  disjoint support, at all places of k(t) of degree at most D. }
  requirege D, 0;
  LIs := LocalInformation(E);
  for LI in LIs do
    for M_e in Conductor(X) do
      require Minimum(LI[1]) ne M_e[1]:
        "The conductors of E and X do not have disjoint support.";
    end for;
  end for;
  return EulerFactorsWithLI_(E, X, LIs, D);
end intrinsic;

function LDegreeWithLI_(E, X, LIs)
  return 2 * LDegree(X) + LDegreeWithLI(E, LIs) + 4;
end function;

intrinsic LDegree(E :: CrvEll[FldFunRat[FldFin]], X :: GrpDrchFFElt)
  -> RngUPolElt
{ The value deg P(E, X, T) - deg Q(E, X, T) for an elliptic curve E over k(t)
  twisted by a Dirichlet character X, assuming that the conductors of E and X
  have disjoint support, with formal L-function L(E, X, T) such that
  L(E, X, T) Q(E, X, T) = P(E, X, T) for some univariate polynomials P(E, X, T)
  and Q(E, X, T) over k. }
  LIs := LocalInformation(E);
  for LI in LIs do
    for M_e in Conductor(X) do
      require Minimum(LI[1]) ne M_e[1]:
        "The conductors of E and X do not have disjoint support.";
    end for;
  end for;
  return LDegreeWithLI_(E, X, LIs);
end intrinsic;

intrinsic LFunction(E :: CrvEll[FldFunRat[FldFin]], X :: GrpDrchFFElt :
    FunctionalEquation := false) -> RngUPolElt
{ The formal L-function L(E, X, T) of an elliptic curve E over k(t) twisted by a
  Dirichlet character X, assuming that the conductors of E and X have disjoint
  support and are not both trivial. If the FunctionalEquation
  L(E, X, T) = e(E x X) q^(d(E x X)) T^(d(E x X)) L(E, X, 1 / q^2 T)-bar is
  true, then the necessary computation is decreased significantly. By default,
  FunctionalEquation is set to be false, since this has not been implemented. }
  LIs := LocalInformation(E);
  require LIs ne [] or Conductor(X) ne []:
    "The conductors of E and X are both trivial.";
  for LI in LIs do
    for M_e in Conductor(X) do
      require Minimum(LI[1]) ne M_e[1]:
        "The conductors of E and X do not have disjoint support.";
    end for;
  end for;
  if FunctionalEquation then
    require false: "The functional equation has not been implemented.";
  else
    D := LDegree(E, X);
    return LFunction(EulerFactorsWithLI_(E, X, LIs, D), D);
  end if;
end intrinsic;