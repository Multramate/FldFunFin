/***
L-FUNCTIONS OF ELLIPTIC CURVES OVER GLOBAL FUNCTION FIELDS

This file defines the trace of Frobenius for the reduction of an elliptic curve
over a global function field at any place including infinity.
***/

function TraceOfFrobeniusAtInfinity(E)
  R<t> := BaseRing(E);
  invariants := [];
  for i := 1 to 5 do
    invariants[i] := Evaluate(hom<R -> R | 1 / t>(aInvariants(E)[i]), 0);
  end for;
  return 1 - #EllipticCurve(invariants) + #BaseRing(R);
end function;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat]) -> RngIntElt
{ The trace of Frobenius for the reduction of E at infinity. }
  R<t> := BaseRing(E);
  li, E := LocalInformation(E, 1 / t);
  require ReductionType(li[5])[1] eq "G":
    "The curve has bad reduction at infinity";
  return TraceOfFrobeniusAtInfinity(E);
end intrinsic;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat], p :: FldFunRatUElt)
  -> RngIntElt
{ The trace of Frobenius a_p for the reduction of E at the place p. }
  R<t> := BaseRing(E);
  require p eq 1 / t or Denominator(p) eq 1:
    "The place is neither a prime nor the place at infinity";
  return p eq 1 / t select TraceOfFrobenius(E)
    else TraceOfFrobenius(E, IntegerRing(R) ! p);
end intrinsic;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat], p :: PlcFunElt) -> RngIntElt
{ " }
  return TraceOfFrobenius(E, BaseRing(E) ! Minimum(p));
end intrinsic;