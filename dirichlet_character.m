/*
L-FUNCTIONS OF DIRICHLET CHARACTERS OVER GLOBAL FUNCTION FIELDS

This file defines some intrinsics for working with Dirichlet characters over the
global function field k(t) of the projective line over k, which has a unique
place at infinity 1 / t.
*/

function EulerPhiWithF(FM)
  q := #BaseRing(Universe(FM)[1]);
  phi := 1;
  for m in FM do
    q_f := q ^ Degree(m[1]);
    phi *:= q_f ^ (m[2] - 1) * (q_f - 1);
  end for;
  return phi;
end function;

intrinsic EulerPhi(M :: RngUPolElt[FldFin]) -> RngIntElt
{ The Euler totient function Phi(M) over k(t) for a non-zero polynomial M in
  k[t]. This is the order of the unit group of k[t] / M. }
  require M ne 0: "The modulus M is the zero polynomial.";
  return EulerPhiWithF(Factorization(M));
end intrinsic;
