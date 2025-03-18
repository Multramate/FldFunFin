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

This file defines the traces of Frobenius and local Euler factors for an
elliptic curve over the global function field k(t) of the projective line over
k, which has a unique place at infinity 1 / t.
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
    return TraceOfFrobenius(E, IntegerRing(K) ! v);
  end if;
  _, E := LocalInformation(E, 1 / t);
  invariants := [];
  for i := 1 to 5 do
    invariants[i] := Evaluate(hom<K -> K | 1 / t>(aInvariants(E)[i]), 0);
  end for;
  return 1 - #EllipticCurve(invariants) + #BaseRing(K);
end function;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat], v :: FldFunRatUElt)
  -> RngIntElt
{ The trace of Frobenius a_v(E) for the reduction of an elliptic curve E over
  k(t) at an element v of k(t), which must either be a prime element of k[t] or
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
  k(t) at 1 / t. Note that this returns 1 if it is split multiplicative, -1 if
  it is non-split multiplicative, and 0 if it is additive. }
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

intrinsic EulerFactor(E :: CrvEll[FldFunRat], v :: FldFunRatUElt :
    Degree := Degree(v), Precision := Infinity()) -> RngUPolElt
{ The Euler factor L_v(E, T^D) of an elliptic curve E over k(t) at an element v
  of k(t), which must either be a prime element of k[t] or 1 / t, where D is
  some integral Degree. If Precision is set to be finite, then this is truncated
  to a polynomial of degree at most Precision, By default, Degree is set to be
  the degree of the place associated to v and Precision is set to be infinity. }
  K<t> := BaseRing(E);
  require Denominator(v) eq 1 or v eq 1 / t:
    "The place v is neither an element of k[t] nor 1 / t";
  requirege Degree, 0;
  requirege Precision, 0;
  return EulerFactorWithLI(E, LocalInformation(E), v, Degree, Precision);
end intrinsic;

intrinsic EulerFactor(E :: CrvEll[FldFunRat], v :: PlcFunElt :
    Degree := Degree(v), Precision := Infinity()) -> RngUPolElt
{ The Euler factor L_v(E, T^D) of an elliptic curve E over k(t) at a place v of
  k(t), where D is some integral Degree. If Precision is set to be finite, then
  this is truncated to a polynomial of degree at most Precision. By default,
  Degree is set to be the degree of v and Precision is set to be infinity. }
  K<t> := BaseRing(E);
  return EulerFactor(E, K ! Minimum(v) : Degree := Degree,
      Precision := Precision);
end intrinsic;

intrinsic EulerFactor(E :: CrvEll[FldFunRat] : Degree := 1,
    Precision := Infinity()) -> RngIntElt
{ The Euler factor L_v(E, T^D) of an elliptic curve E over k(t) at 1 / t, where
  D is some integral Degree. If Precision is set to be finite, then this is
  truncated to a polynomial of degree at most Precision. By default, Degree is
  set to be 1 and Precision is set to be infinity. }
  K<t> := BaseRing(E);
  return EulerFactor(E, 1 / t : Degree := 1, Precision := Precision);
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