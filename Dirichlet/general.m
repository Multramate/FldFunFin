/* GENERAL INTRINSICS FOR DIRICHLET CHARACTERS OVER GLOBAL FUNCTION FIELDS

This file defines some general intrinsics relevant for Dirichlet characters of a
non-zero modulus M in k[t] over the global function field k(t) of the projective
line over a finite field k, which includes:
- AllMonicPolynomials: the set of all monic polynomials over k of some degree
- EulerPhi: the size of the unit group of k[t] / M
- Log: the discrete logarithm in the unit group of k[t] / M
- IsGenerator: checks if an element of k[t] / M is a generator of its unit group
- Generators: the set of generators of the unit group of k[t] / M
- MinimalGenerator: the minimal generator of the unit group of k[t] / M
- RandomGenerator: a random generator of the unit group of k[t] / M
*/

intrinsic AllMonicPolynomials(k :: FldFin, D :: RngIntElt)
  -> SetEnum[RngUPolElt[FldFin]]
{ The set of all monic polynomials over a finite field k of degree D. }
  R<t> := PolynomialRing(k);
  return {t ^ D + R ! s : s in Subsequences(Set(k), D)};
end intrinsic;

function EulerPhiWithF(fac)
  q := #BaseRing(Universe(fac)[1]);
  phi := 1;
  for m in fac do
    q_f := q ^ Degree(m[1]);
    phi *:= q_f ^ (m[2] - 1) * (q_f - 1);
  end for;
  return phi;
end function;

intrinsic EulerPhi(M :: RngUPolElt[FldFin]) -> RngIntElt
{ The Euler totient function Phi(M) over k(t) for a non-zero modulus M in k[t].
  This is the size of the unit group of k[t] / M. }
  require M ne 0: "The modulus M is the zero polynomial of k[t].";
  return EulerPhiWithF(Factorization(Numerator(M)));
end intrinsic;

intrinsic EulerPhi(M :: FldFunRatUElt[FldFin]) -> RngIntElt
{ " }
  require Denominator(M) eq 1: "The modulus M is not an element of k[t].";
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
      return -3; // there are no positive integers n such that b^n = x
    end if;
  end for;
  return -2; // the element x is not a unit of k[t] / M
end function;

intrinsic Log(M :: RngUPolElt[FldFin], b :: Any, x :: Any) -> RngIntElt
{ The discrete logarithm log_b(x) for a base b and an element x of k[t] that are
  units when reduced modulo a non-zero irreducible modulus M in k[t]. This is
  the smallest non-negative integer n such that b^n = x. }
  require IsIrreducible(M): "The modulus M is not a prime element of k[t].";
  R<t> := Parent(M);
  require IsCoercible(R, b): "The base b is not an element of k[t].";
  require IsCoercible(R, x): "The element x is not an element of k[t].";
  n := LogWithMod(M, R ! b mod M, R ! x mod M);
  require n ne -1: "The base b is not a unit of k[t] / M.";
  require n ne -2: "The element x is not a unit of k[t] / M.";
  require n ne -3: "There are no positive integers n such that b^n = x.";
  return n;
end intrinsic;

intrinsic Log(M :: FldFunRatUElt[FldFin], b :: Any, x :: Any) -> RngIntElt
{ " }
  require Denominator(M) eq 1: "The modulus M is not an element of k[t].";
  return Log(Numerator(M), b, x);
end intrinsic;

function IsGeneratorWithPhi(M, x, phi, fac)
  return Modexp(x, phi, M) eq 1 and &and[Modexp(x, m, M) ne 1 : m in fac];
end function;

intrinsic IsGenerator(M :: RngUPolElt[FldFin], x :: Any) -> BoolElt
{ The predicate that checks whether an element x in k[t] / M for a non-zero
  modulus M in k[t] is a generator of its unit group. }
  R<t> := Parent(M);
  require IsCoercible(R, x): "The element x is not an element of k[t].";
  phi := EulerPhi(M);
  return IsGeneratorWithPhi(M, R ! x mod M, phi,
      [phi div m[1] : m in Factorization(phi)]);
end intrinsic;

intrinsic IsGenerator(M :: FldFunRatUElt[FldFin], x :: Any) -> BoolElt
{ " }
  require Denominator(M) eq 1: "The modulus M is not an element of k[t].";
  return IsGenerator(Numerator(M), x);
end intrinsic;

function GeneratorsWithPhi(M, phi, fac)
  R<t> := Parent(M);
  k := Set(BaseRing(R));
  return {R ! x : x in Subsequences(k, Degree(M)) |
      IsGeneratorWithPhi(M, R ! x mod M, phi, fac)};
end function;

intrinsic Generators(M :: RngUPolElt[FldFin]) -> SetEnum[RngUPolElt[FldFin]]
{ The finite set of generators of the unit group of k[t] / M for a non-zero
  modulus M in k[t]. }
  phi := EulerPhi(M);
  return GeneratorsWithPhi(M, phi, [phi div m[1] : m in Factorization(phi)]);
end intrinsic;

intrinsic Generators(M :: FldFunRatUElt[FldFin]) -> SetEnum[RngUPolElt[FldFin]]
{ " }
  require Denominator(M) eq 1: "The modulus M is not an element of k[t].";
  return Generators(Numerator(M));
end intrinsic;

function MinimalGeneratorWithPhi(M, phi, fac)
  return Minimum(GeneratorsWithPhi(M, phi, fac));
end function;

intrinsic MinimalGenerator(M :: RngUPolElt[FldFin]) -> RngUPolElt[FldFin]
{ The generator of the unit group of k[t] / M for a non-zero modulus M in k[t]
  that is minimal with respect to the ordering on polynomials over k. }
  phi := EulerPhi(M);
  return
    MinimalGeneratorWithPhi(M, phi, [phi div m[1] : m in Factorization(phi)]);
end intrinsic;

intrinsic MinimalGenerator(M :: FldFunRatUElt[FldFin]) -> RngUPolElt[FldFin]
{ " }
  require Denominator(M) eq 1: "The modulus M is not an element of k[t].";
  return MinimalGenerator(Numerator(M));
end intrinsic;

function RandomGeneratorWithPhi(M, phi, fac)
  return Random(GeneratorsWithPhi(M, phi, fac));
end function;

intrinsic RandomGenerator(M :: RngUPolElt[FldFin]) -> RngUPolElt[FldFin]
{ A generator of the unit group of k[t] / M for a non-zero modulus M in k[t]. }
  phi := EulerPhi(M);
  return
    RandomGeneratorWithPhi(M, phi, [phi div m[1] : m in Factorization(phi)]);
end intrinsic;

intrinsic RandomGenerator(M :: FldFunRatUElt[FldFin]) -> RngUPolElt[FldFin]
{ " }
  require Denominator(M) eq 1: "The modulus M is not an element of k[t].";
  return RandomGenerator(Numerator(M));
end intrinsic;