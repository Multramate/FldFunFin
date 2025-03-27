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

intrinsic EulerPhi(M :: FldFunRatUElt[FldFin]) -> RngIntElt
{ The Euler totient function Phi(M) over k(t) for a non-zero polynomial M in
  k[t]. This is the order of the unit group of k[t] / M. }
  require Denominator(M) eq 1: "The modulus M is not a polynomial.";
  require M ne 0: "The modulus M is the zero polynomial.";
  return EulerPhiWithF(Factorization(Numerator(M)));
end intrinsic;

function LogWithPhi(phi, b, x)
  b_n := 1;
  for n := 0 to phi - 1 do
    if b_n eq x then
      return n;
    end if;
    b_n *:= b;
    if b_n eq 0 then
      return -1; // the base b is not a unit
    end if;
    if b_n eq 1 then
      return -2; // the base b is not a generator
    end if;
  end for;
  return -3; // the element x is not a unit
end function;

intrinsic Log(M :: FldFunRatUElt[FldFin], b :: FldFunRatUElt[FldFin],
    x :: FldFunRatUElt[FldFin]) -> RngIntElt
{ The discrete logarithm log_b(x) for a base b and an element x in the unit
  group of k[t] / M for a non-zero irreducible polynomial M in k[t]. This is the
  smallest positive integer n such that b^n = x. }
  require Denominator(M) eq 1: "The modulus M is not a polynomial.";
  require IsIrreducible(Numerator(M)): "The modulus M is not irreducible.";
  require Denominator(b) eq 1: "The base b is not a polynomial.";
  b := quo<Parent(Numerator(M)) | M> ! Numerator(b);
  require Denominator(x) eq 1: "The base x is not a polynomial.";
  x := quo<Parent(Numerator(M)) | M> ! Numerator(x);
  n := LogWithPhi(EulerPhi(M), b, x);
  require n ne -1: "The base b is not a unit.";
  require n ne -2: "The base b is not a generator.";
  require n ne -3: "The element x is not a unit.";
  return n;
end intrinsic;

function DirichletCharacterFunc(M, g, h, x)
  return Numerator(x) mod Numerator(M) eq 0 select 0 else h ^ Log(M, g, x);
end function;

intrinsic DirichletCharacter(M :: FldFunRatUElt[FldFin],
    g :: FldFunRatUElt[FldFin], h :: FldCycElt[FldRat]) -> Map
{ The Dirichlet character over k(t) of modulus M for a non-zero irreducible
  polynomial M in k[t], given by mapping a generator g in the unit group of
  k[t] / M to an element h in a cyclotomic field over Q. }
  require Denominator(M) eq 1: "The modulus M is not a polynomial.";
  require IsIrreducible(Numerator(M)): "The modulus M is not irreducible.";
  require h ^ EulerPhi(M) eq 1:
    "The order of the element h does not divide the order of the generator g.";
  require Denominator(g) eq 1: "The generator g is not a polynomial.";
  return func<x | DirichletCharacterFunc(M, g, h, x)>;
end intrinsic;