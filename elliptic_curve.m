/***
L-FUNCTIONS OF ELLIPTIC CURVES OVER GLOBAL FUNCTION FIELDS

This file defines the trace of Frobenius and its associated local Euler factor
for the reduction of an elliptic curve over a global function field at any place
including infinity.
***/

function TraceOfFrobeniusAtInfinity(E)
  K<t> := BaseRing(E);
  invariants := [];
  for i := 1 to 5 do
    invariants[i] := Evaluate(hom<K -> K | 1 / t>(aInvariants(E)[i]), 0);
  end for;
  return 1 - #EllipticCurve(invariants) + #BaseRing(K);
end function;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat]) -> RngIntElt
{ The trace of Frobenius a_oo for the reduction of the elliptic curve E over a
  global function field at infinity. }
  K<t> := BaseRing(E);
  li, E := LocalInformation(E, 1 / t);
  require ReductionType(li[5])[1] eq "G":
    "The curve E has bad reduction at infinity";
  return TraceOfFrobeniusAtInfinity(E);
end intrinsic;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat], P :: FldFunRatUElt)
  -> RngIntElt
{ The trace of Frobenius a_P for the reduction of the elliptic curve E over a
  global function field at the place P. }
  K<t> := BaseRing(E);
  require P eq 1 / t or Denominator(P) eq 1:
    "The place P is neither a prime nor the place at infinity";
  return P eq 1 / t select TraceOfFrobenius(E)
    else TraceOfFrobenius(E, IntegerRing(K) ! P);
end intrinsic;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat], P :: PlcFunElt) -> RngIntElt
{ " }
  return TraceOfFrobenius(E, BaseRing(E) ! Minimum(P));
end intrinsic;

function EulerFactor(E, lis, P, p)
  R<T> := PolynomialRing(IntegerRing());
  D := Degree(P);
  if p lt D then
    return R ! 1;
  end if;
  K<t> := BaseRing(E);
  T_D := T ^ D;
  for li in lis do
    if K ! P eq Minimum(li[1]) then
      return ReductionType(li[5])[1] eq "A" select R ! 1
        else (li[6] select 1 - T_D else 1 + T_D);
    end if;
  end for;
  return 1 - TraceOfFrobenius(E, P) * T_D
    + (p lt 2 * D select 0 else #BaseRing(K) ^ D * T_D ^ 2);
end function;

intrinsic EulerFactor(E :: CrvEll[FldFunRat], P :: FldFunRatUElt :
  Precision := Infinity()) -> RngUPolElt
{ The Euler factor of the elliptic curve E over a global function field at the
  place P. }
  K<t> := BaseRing(E);
  require P eq 1 / t or Denominator(P) eq 1:
    "The place P is neither a prime nor the place at infinity";
  return EulerFactor(E, LocalInformation(E), P, Precision);
end intrinsic;

intrinsic EulerFactor(E :: CrvEll[FldFunRat], P :: PlcFunElt :
  Precision := Infinity()) -> RngUPolElt
{ " }
  return EulerFactor(E, LocalInformation(E), BaseRing(E) ! Minimum(P),
      Precision);
end intrinsic;