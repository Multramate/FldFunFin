/***
L-FUNCTIONS OF ELLIPTIC CURVES OVER GLOBAL FUNCTION FIELDS
***/

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat]) -> RngIntElt
{ The trace of Frobenius for the reduction of E at infinity. }
  R<t> := BaseRing(E);
  _, E := LocalInformation(E, 1 / t);
  invariants := [];
  for i := 1 to 5 do
    invariants[i] := Evaluate(hom<R -> R | 1 / t>(aInvariants(E)[i]), 0);
  end for;
  return 1 - #EllipticCurve(invariants) + #BaseRing(R);
end intrinsic;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat], p :: FldFunRatUElt)
  -> RngIntElt
{ The trace of Frobenius a_p for the reduction of E at the place p. }
  R<t> := BaseRing(E);
  require p eq 1 / t or Denominator(p) eq 1: "p is not a place";
  return p eq 1 / t select TraceOfFrobenius(E) else TraceOfFrobenius(E, p);
end intrinsic;

intrinsic TraceOfFrobenius(E :: CrvEll[FldFunRat], p :: PlcFunElt) -> RngIntElt
{ " }
  return TraceOfFrobenius(E, Minimum(p));
end intrinsic;