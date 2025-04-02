/*
L-FUNCTIONS OF ELLIPTIC CURVES OVER GLOBAL FUNCTION FIELDS

Let E be an elliptic curve over a global function field K of a smooth proper
geometrically irreducible curve of genus g over a finite field k of order q. The
motive h^1(E)(1) associated to E is self dual with w(E) := w(h^1(E)(1)) = 1,
whose l-adic realisation is the dual H_l(E) of the two-dimensional l-adic
rational Tate module of E. This has geometric Galois invariants precisely when E
is a constant elliptic curve arising as the base change of some base elliptic
curve E' over k, in which case the formal L-function L(E, T) of E is precisely
1 / Q(T) Q(q T), where Q(T) is the numerator of the zeta-function of E'.

In general, the local Euler factor L_v(E, T) of E at a place v of K depends on
the reduction E_v of a model of E that is minimal at v. If E has good reduction
at v, then the trace of Frobenius a_v(E) at v acting on H_l(E) is
1 - #E_v + q_v, where q_v is the order of the residue field at v, in which case
L_v(E, T) is given by 1 - a_v(E) T + q_v T^2. Otherwise, a_v(E) is 1 if the
reduction is split multiplicative, -1 if it is non-split multiplicative, and 0
if it is additive, in which case L_v(E, T) is given by 1 - a_v(E) T.

It remains to compute the global root number e(E) := e(h^1(E)(1)) of E for the
functional equation L(E, T) = e(E) q^d(E) T^d(E) L(E, 1 / q^2 T), where
d(E) := d(h^1(E)(1)) is (4 g - 4) + deg f(h^1(E)(1)). This is the product of
local root numbers e_v(E) of the places v of K where E has bad reduction, with
explicit formulae in terms of Kronecker symbols (-, q_v) when the characteristic
is different from 2 and 3. If the reduction is potentially good, then the
greatest common divisor g_v(E) between 12 and the valuation of the discriminant
of E_v can only take the values 2, 3, 4, 6, 12, and in particular e_v(E) is 1 if
g_v(E) = 12, (-3, q_v) if g_v(E) = 4, (-2, q_v) if g_v(E) = 3, and (-1, q_v)
otherwise. Otherwise, e_v(E) is -1 if the reduction is split multiplicative, 1
if it is non-split multiplicative, and (-1, q_v) if it is additive.

This file defines some intrinsics that compute the formal L-function of an
elliptic curve over the global function field k(t) of the projective line over
k, which has a unique place at infinity 1 / t. This includes generalised traces
of Frobenius, local and global Euler factors, and local and global root numbers.
*/

function TraceOfFrobeniusWithLI(E, LIs, v)
  K<t> := BaseRing(E);
  k<a> := BaseRing(K);
  for LI in LIs do
    if K ! v eq Minimum(LI[1]) then
      return ReductionType(LI[5])[1] eq "A" select 0
        else LI[6] select 1 else -1;
    end if;
  end for;
  if v ne 1 / t then
    return TraceOfFrobenius(E, Numerator(v));
  end if;
  _, E := LocalInformation(E, 1 / t);
  invariants := [];
  for i := 1 to 5 do
    invariants[i] := Evaluate(hom<K -> K | 1 / t>(aInvariants(E)[i]), 0);
  end for;
  return 1 - #EllipticCurve(invariants) + #BaseRing(K);
end function;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat], v :: FldFunRatUElt[FldFin])
  -> RngIntElt
{ The trace of Frobenius a_v(E) for the reduction of an elliptic curve E over
  k(t) at a place v of k(t), which must either be a prime element of k[t] or
  1 / t. Note that this returns 1 if it is split multiplicative, -1 if it is
  non-split multiplicative, and 0 if it is additive. }
  K<t> := BaseRing(E);
  require Denominator(v) eq 1 or v eq 1 / t:
    "The place v is neither an element of k[t] nor 1 / t";
  return TraceOfFrobeniusWithLI(E, LocalInformation(E), v);
end intrinsic;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat], v :: PlcFunElt) -> RngIntElt
{ The trace of Frobenius a_v(E) for the reduction of an elliptic curve E over
  k(t) at a place v of k(t). Note that this returns 1 if it is split
  multiplicative, -1 if it is non-split multiplicative, and 0 if it is
  additive. }
  K<t> := BaseRing(E);
  return TraceOfFrobenius(E, K ! Minimum(v));
end intrinsic;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat]) -> RngIntElt
{ The trace of Frobenius a_v(E) for the reduction of an elliptic curve E over
  k(t) at v = 1 / t. Note that this returns 1 if it is split multiplicative, -1
  if it is non-split multiplicative, and 0 if it is additive. }
  K<t> := BaseRing(E);
  return TraceOfFrobenius(E, 1 / t);
end intrinsic;

function EulerFactorWithLI(E, LIs, v, D, P)
  R<T> := PolynomialRing(IntegerRing());
  if P lt D then
    return R ! 1;
  end if;
  T_D := T ^ D;
  if P lt 2 * D then
    return 1 - TraceOfFrobeniusWithLI(E, LIs, v) * T_D;
  end if;
  K<t> := BaseRing(E);
  k<a> := BaseRing(K);
  for LI in LIs do
    if K ! v eq Minimum(LI[1]) then
      return 1 - TraceOfFrobeniusWithLI(E, LIs, v) * T_D;
    end if;
  end for;
  return 1 - TraceOfFrobeniusWithLI(E, LIs, v) * T_D + #k ^ D * T_D ^ 2;
end function;

intrinsic EulerFactor(E :: CrvEll[FldFunRat], v :: FldFunRatUElt[FldFin] :
    Exponent := Degree(v), Precision := Infinity()) -> RngUPolElt
{ The Euler factor L_v(E, T^D) of an elliptic curve E over k(t) at a place v of
  k(t), which must either be a prime element of k[t] or 1 / t, where D is some
  Exponent. If Precision is set to be finite, then this is truncated to a
  polynomial of degree at most Precision, By default, Exponent is set to be
  the degree of the place associated to v and Precision is set to be infinity. }
  K<t> := BaseRing(E);
  require Denominator(v) eq 1 or v eq 1 / t:
    "The place v is neither an element of k[t] nor 1 / t";
  requirege Exponent, 0;
  return EulerFactorWithLI(E, LocalInformation(E), v, Exponent, Precision);
end intrinsic;

intrinsic EulerFactor(E :: CrvEll[FldFunRat], v :: PlcFunElt :
    Exponent := Degree(v), Precision := Infinity()) -> RngUPolElt
{ The Euler factor L_v(E, T^D) of an elliptic curve E over k(t) at a place v of
  k(t), where D is some Exponent. If Precision is set to be finite, then this is
  truncated to a polynomial of degree at most Precision. By default, Exponent is
  set to be the degree of v and Precision is set to be infinity. }
  K<t> := BaseRing(E);
  return EulerFactor(E, K ! Minimum(v) : Exponent := Exponent,
      Precision := Precision);
end intrinsic;

intrinsic EulerFactor(E :: CrvEll[FldFunRat] : Exponent := 1,
    Precision := Infinity()) -> RngIntElt
{ The Euler factor L_v(E, T^D) of an elliptic curve E over k(t) at v = 1 / t,
  where D is some Exponent. If Precision is set to be finite, then this is
  truncated to a polynomial of degree at most Precision. By default, Exponent is
  set to be 1 and Precision is set to be infinity. }
  K<t> := BaseRing(E);
  return EulerFactor(E, 1 / t : Exponent := 1, Precision := Precision);
end intrinsic;

function EulerFactorsWithLI(E, LIs, D)
  K<t> := BaseRing(E);
  k<a> := BaseRing(K);
  S := [PolynomialRing(IntegerRing()) | ];
  if D gt 0 then
    Append(~S, EulerFactorWithLI(E, LIs, 1 / t, 1, D));
  end if;
  for i := 1 to D do
    for v in AllIrreduciblePolynomials(k, i) do
      Append(~S, EulerFactorWithLI(E, LIs, K ! v, Degree(v), D));
    end for;
  end for;
  return S;
end function;

intrinsic EulerFactors(E :: CrvEll[FldFunRat], D :: RngIntElt)
  -> SeqEnum[RngUPolElt]
{ The finite set of all Euler factors of an elliptic curve E over k(t) at all
  places of k(t) of degree at most D. }
  requirege D, 0;
  return EulerFactorsWithLI(E, LocalInformation(E), D);
end intrinsic;

function LocalRootNumberWithLI(E, LI)
  K<t> := BaseRing(E);
  k<a> := BaseRing(K);
  d := Degree(LI[1]);
  if Valuation(jInvariant(E), LI[1]) ge 0 then
    g := GCD(LI[2], 12);
    return g eq 12 select 1 else
      KroneckerSymbol(g eq 4 select -3 else g eq 3 select -2 else -1, #k) ^ d;
  else
    return ReductionType(LI[5])[1] eq "A" select KroneckerSymbol(-1, #k) ^ d
      else LI[6] select -1 else 1;
  end if;
end function;

intrinsic LocalRootNumber(E :: CrvEll[FldFunRat], v :: FldFunRatUElt[FldFin])
  -> RngIntElt
{ The local root number e_v(E) of an elliptic curve E over k(t) at a place v of
  k(t), which must either be a prime element of k[t] or 1 / t. Note that this
  has not been implemented for characteristic 2 and 3. }
  K<t> := BaseRing(E);
  require Characteristic(K) gt 3:
    "This has not been implemented for characteristic 2 and 3";
  require Denominator(v) eq 1 or v eq 1 / t:
    "The place v is neither an element of k[t] nor 1 / t";
  return LocalRootNumberWithLI(E, LocalInformation(E, v));
end intrinsic;

intrinsic LocalRootNumber(E :: CrvEll[FldFunRat], v :: PlcFunElt) -> RngIntElt
{ The local root number e_v(E) of an elliptic curve E over k(t) at a place v of
  k(t). Note that this has not been implemented for characteristic 2 and 3. }
  K<t> := BaseRing(E);
  return LocalRootNumber(E, K ! Minimum(v));
end intrinsic;

intrinsic LocalRootNumber(E :: CrvEll[FldFunRat]) -> RngIntElt
{ The local root number e_v(E) of an elliptic curve E over k(t) at v = 1 / t.
  Note that this has not been implemented for characteristic 2 and 3. }
  K<t> := BaseRing(E);
  return LocalRootNumber(E, 1 / t);
end intrinsic;

function RootNumberWithLI(E, LIs)
  return &*[IntegerRing() | LocalRootNumberWithLI(E, LI) : LI in LIs];
end function;

intrinsic RootNumber(E :: CrvEll[FldFunRat]) -> RngIntElt
{ The global root number e(E) of an elliptic curve E over k(t). Note that this
  has not been implemented for characteristic 2 and 3. }
  K<t> := BaseRing(E);
  require Characteristic(K) gt 3:
    "This has not been implemented for characteristic 2 and 3";
  return RootNumberWithLI(E, LocalInformation(E));
end intrinsic;

function LDegreeWithLI(E, LIs)
  return &+[IntegerRing() | Degree(LI[1]) * LI[3] : LI in LIs] - 4;
end function;

intrinsic LDegree(E :: CrvEll[FldFunRat]) -> RngUPolElt
{ The value deg P(E, T) - deg Q(E, T) for an elliptic curve E over k(t) with
  formal L-function L(E, T) such that L(E, T) Q(E, T) = P(E, T) for some
  univariate polynomials P(E, T) and Q(E, T) over k. }
  return LDegreeWithLI(E, LocalInformation(E));
end intrinsic;

intrinsic LFunction_(E :: CrvEll[FldFunRat] : FunctionalEquation := true)
  -> RngUPolElt
{ The formal L-function L(E, T) of a elliptic curve E over k(t). If E is a
  constant elliptic curve arising as the base change of some base elliptic
  curve E' over k, then this returns 1 / Q(T) Q(q T), where Q(T) is the
  numerator of the zeta-function of E'. Otherwise, if the FunctionalEquation
  L(E, T) = e(E) q^(d(E)) T^(d(E)) L(E, 1 / q^2 T) is true, then the necessary
  computation is decreased significantly. By default, FunctionalEquation is set
  to be true, but this has not been implemented for characteristic 2 and 3. }
  constant, E_ := IsConstantCurve(E);
  if constant then
    L<T> := LPolynomial(E_);
    return 1 / (L * Evaluate(L, #BaseRing(E_) * T));
  end if;
  K<t> := BaseRing(E);
  k<a> := BaseRing(K);
  LIs := LocalInformation(E);
  D := LDegreeWithLI(E, LIs);
  if FunctionalEquation then
    require Characteristic(K) gt 3:
      "This has not been implemented for characteristic 2 and 3";
    return LFunction(EulerFactorsWithLI(E, LIs, Floor(D / 2)), D :
        FunctionalEquation := true,
        EpsilonFactor := RootNumberWithLI(E, LIs) * #k ^ D,
        WeightFactor := 1 / #k ^ 2, DualAutomorphism := func<x | x>);
  else
    return LFunction(EulerFactorsWithLI(E, LIs, D), D);
  end if;
end intrinsic;