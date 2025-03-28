/*
L-FUNCTIONS OF DIRICHLET CHARACTERS OVER GLOBAL FUNCTION FIELDS

This file defines some intrinsics for working with Dirichlet characters over the
global function field k(t) of the projective line over k, which has a unique
place at infinity 1 / t.
*/

declare type GrpDrchFFElt;

declare attributes GrpDrchFFElt: BaseRing, BaseField, Modulus, Generator, Image;

intrinsic DirichletCharacter(M :: RngUPolElt[FldFin], g :: Any, h :: Any)
  -> GrpDrchFFElt
{ The Dirichlet character over k(t) of modulus a non-zero irreducible polynomial
  M in k[t], given by mapping an element g in k[t] that is a unit and a
  generator when reduced modulo M, to an element h that is a complex number. }
  R<t> := Parent(M);
  require IsIrreducible(M): "The modulus M is not irreducible in k[t].";
  require IsCoercible(R, g): "The generator g is not a polynomial in k[t].";
  require IsCoercible(ComplexField(), h):
    "The element h is not a complex number.";
  X := New(GrpDrchFFElt);
  X`BaseRing := R;
  X`Modulus := M;
  X`Generator := g;
  X`Image := h;
  return X;
end intrinsic;

intrinsic DirichletCharacter(M :: FldFunRatUElt[FldFin], g :: Any, h :: Any)
  -> Map
{ " }
  require Denominator(M) eq 1: "The modulus M is not a polynomial in k[t].";
  return DirichletCharacter(Numerator(M), g, h);
end intrinsic;

intrinsic Print(X :: GrpDrchFFElt)
{ Print a Dirichlet character over k(t). }
  R<t> := X`BaseRing;
  printf
    "Dirichlet character over F_%o(%o) of modulus %o given by mapping %o to %o",
    Characteristic(R), t, X`Modulus, X`Generator, X`Image;
end intrinsic;

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
{ The Euler totient function Phi(M) over k(t) for a non-zero modulus M in k[t].
  This is the order of the unit group of k[t] / M. }
  require M ne 0: "The modulus M is the zero polynomial in k[t].";
  return EulerPhiWithF(Factorization(Numerator(M)));
end intrinsic;

intrinsic EulerPhi(M :: FldFunRatUElt[FldFin]) -> RngIntElt
{ " }
  require Denominator(M) eq 1: "The modulus M is not a polynomial in k[t].";
  return EulerPhi(Numerator(M));
end intrinsic;

function LogWithMod(M, b, x)
  b_n := 1;
  phi := EulerPhi(M) - 1;
  for n := 0 to phi do
    if b_n eq x then
      return n;
    end if;
    b_n := b_n * b mod M;
    if b_n eq 0 then
      return -1; // the base b is not a unit of k[t] / M
    end if;
    if b_n eq 1 then
      return -3; // there are no positive integers n such that b ^ n = x
    end if;
  end for;
  return -2; // the element x is not a unit of k[t] / M
end function;

intrinsic Log(M :: RngUPolElt[FldFin], b :: Any, x :: Any) -> RngIntElt
{ The discrete logarithm log_b(x) for a base b and an element x in k[t] that are
  units when reduced modulo a non-zero irreducible modulus M in k[t]. This is
  the smallest positive integer n such that b ^ n = x. }
  require IsIrreducible(M): "The modulus M is not irreducible in k[t].";
  R<t> := Parent(M);
  require IsCoercible(R, b): "The base b is not a polynomial in k[t].";
  require IsCoercible(R, x): "The element x is not a polynomial in k[t].";
  n := LogWithMod(M, R ! b mod M, R ! x mod M);
  require n ne -1: "The base b is not a unit of k[t] / M.";
  require n ne -2: "The element x is not a unit of k[t] / M.";
  require n ne -3: "There are no positive integers n such that b ^ n = x.";
  return n;
end intrinsic;

intrinsic Log(M :: FldFunRatUElt[FldFin], b :: Any, x :: Any) -> RngIntElt
{ " }
  require Denominator(M) eq 1: "The modulus M is not a polynomial in k[t].";
  return Log(Numerator(M), b, x);
end intrinsic;

intrinsic '@'(x :: Any, X :: GrpDrchFFElt) -> Any
{ Evaluate a Dirichlet character X over k(t) on an element x in k[t]. }
  R<t> := X`BaseRing;
  M := X`Modulus;
  require IsCoercible(R, x): "The element x is not a polynomial in k[t].";
  return R ! x mod M eq 0 select 0 else X`Image ^ Log(M, X`Generator, x);
end intrinsic;