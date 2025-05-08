/* L-FUNCTIONS OF DIRICHLET CHARACTERS OVER GLOBAL FUNCTION FIELDS

Let X be a Dirichlet character over a global function field K of a smooth proper
geometrically irreducible curve of genus g over a finite field k of size q, with
modulus a non-zero element M of k[t]. The motive [X] associated to X has
w(X) := w([X]) = 0, and its l-adic realisation is simply the complex Galois
representation associated to X. Assume for now that M is irreducible.

The conductor of X has support containing the places 1 / t and M. The place
1 / t is ramified on X precisely when X is odd, namely when X is not trivial on
some element of k, in which case the ramification is necessarily tame. The place
M is ramified on X precisely when X is not trivial on a generator of the unit
group of k[t] / M, in which case the ramification is necessarily tame. The
complex Galois representation associated to X has geometric Galois invariants
precisely when X has trivial conductor, in which case the formal L-function
L(X, T) of X is precisely 1 / (1 - T) (1 - q T). In general, the local Euler
factor L_v(X, T) of X at a place v of K is given by 1 - X(v) T, where X(v) is 0
if X is ramified at v, and 1 if v is 1 / t and X is unramified at v.

This file defines some intrinsics that compute the formal L-function of a
Dirichlet character of irreducible moduli over the global function field k(t) of
the projective line over k, which has a unique place at infinity 1 / t. This
includes global root numbers and local Euler factors.
*/

intrinsic CharacterSum(X :: GrpDrchFFElt : D := ResidueDegree(X) - 1)
  -> FldCycElt
{ The character sum of a Dirichlet character X over k(t) of a non-zero modulus M
  in k[t]. This is the sum of X(x) of all monic polynomials x of k[t] of degree
  D. By default, D is set to be deg(M) - 1. }
  if not assigned X`CharacterSum then
    X`CharacterSum := &+[X(f) :
        f in AllMonicPolynomials(ResidueField(X), ResidueDegree(X) - 1)];
  end if;
  return X`CharacterSum;
end intrinsic;

intrinsic EpsilonFactor(X :: GrpDrchFFElt) -> FldCycElt
{ The epsilon factor e(X) q^(d(X) / 2) of a Dirichlet character X over k(t).
  This is the character sum of X if X is odd and its negation otherwise. }
  if not assigned X`EpsilonFactor then
    X`EpsilonFactor := IsEven(X) select -CharacterSum(X) else CharacterSum(X);
  end if;
  return X`EpsilonFactor;
end intrinsic;

intrinsic ResidueGaussSum(X :: GrpDrchFFElt) -> FldCycElt
{ The Gauss sum of the character over k associated to a Dirichlet character X
  over k(t) of characteristic p. This is the sum of X(x) of all non-zero
  elements x of k, weighted by p-th roots of unity raised to the trace of x. }
  if not assigned X`ResidueGaussSum then
    C<z> := CyclotomicField(Characteristic(X));
    X`ResidueGaussSum :=
      &+[ResidueCharacter(X)(x) * z ^ IntegerRing() ! Trace(x) :
        x in ResidueField(X) | x ne 0];
  end if;
  return X`ResidueGaussSum;
end intrinsic;

intrinsic GaussSum(X :: GrpDrchFFElt) -> FldCycElt
{ The Gauss sum of a Dirichlet character X over k(t) of a non-zero modulus M in
  k[t]. This is the sum of X(x) of all elements x of k[t] of degree at most the
  degree of M, weighted by the Hayes exponential function of x / M. }
  if not assigned X`GaussSum then
    X`GaussSum := EpsilonFactor(X)
      * (IsEven(X) select ResidueSize(X) else ResidueGaussSum(X));
  end if;
  return X`GaussSum;
end intrinsic;

intrinsic Conductor(X :: GrpDrchFFElt) -> SeqEnum[Tup]
{ The conductor of a Dirichlet character X over k(t). This is a sequence of
  tuples of the form <M, e>, where M is either a prime element of k[t] or 1 / t,
  and the local conductor exponent e at M is a positive integer. }
  if not assigned X`Conductor then
    X`Conductor := [];
    if IsOdd(X) then
      Append(~X`Conductor, <1 / Domain(X).1, 1>);
    end if;
    if IsPrimitive(X) then
      Append(~X`Conductor, <Modulus(X), 1>);
    end if;
  end if;
  return X`Conductor;
end intrinsic;

intrinsic EulerFactor(X :: GrpDrchFFElt, v :: Any : Exponent := 1,
    Precision := Infinity()) -> RngUPolElt[FldCyc]
{ The Euler factor L_v(X, T^D) of a Dirichlet character X over k(t) at a place v
  of k(t), which must either be a prime element of k[t] or 1 / t, where D is
  some Exponent. If Precision is set to be finite, then this is truncated to a
  polynomial of degree at most Precision, By default, Exponent is set to be 1
  and Precision is set to be infinity. }
  K<t> := Domain(X);
  require IsCoercible(K, v): "The place v is not an element of k(t).";
  v := K ! v;
  require Denominator(v) eq 1 or v eq 1 / t:
    "The place v is neither an element of k[t] nor 1 / t.";
  requirege Exponent, 0;
  R<T> := PolynomialRing(Codomain(X));
  if Precision lt Exponent then
    return R ! 1;
  end if;
  return 1 - X(v) * T ^ Exponent;
end intrinsic;

intrinsic EulerFactor(X :: GrpDrchFFElt : Exponent := 1,
    Precision := Infinity()) -> RngUPolElt[FldCyc]
{ The Euler factor L_v(X, T^D) of a Dirichlet character X over k(t) at
  v = 1 / t, where D is some Exponent. If Precision is set to be finite, then
  this is truncated to a polynomial of degree at most Precision. By default,
  Exponent is set to be 1 and Precision is set to be infinity. }
  return EulerFactor(X, 1 / Domain(X).1 : Exponent := 1,
      Precision := Precision);
end intrinsic;

intrinsic EulerFactors(X :: GrpDrchFFElt, D :: RngIntElt)
  -> SeqEnum[RngUPolElt[FldCyc]]
{ The finite set of all Euler factors of a Dirichlet character X over k(t) at
  all places of k(t) of degree at most D. }
  requirege D, 0;
  k<a> := ResidueField(X);
  S := [PolynomialRing(Codomain(X)) | ];
  if D gt 0 then
    Append(~S, EulerFactor(X, 1 / Domain(X).1 : Precision := D));
  end if;
  for i := 1 to D do
    for v in AllIrreduciblePolynomials(k, i) do
      Append(~S, EulerFactor(X, v : Exponent := Degree(v), Precision := D));
    end for;
  end for;
  return S;
end intrinsic;

intrinsic LDegree(X :: GrpDrchFFElt) -> RngIntElt
{ The value deg P(X, T) - deg Q(X, T) for a Dirichlet character X over k(t) with
  formal L-function L(X, T) such that L(X, T) Q(X, T) = P(X, T) for some
  univariate polynomials P(X, T) and Q(X, T) over k. }
  if not assigned X`LDegree then
    X`LDegree := &+[IntegerRing() |
        M_e[1] eq 1 / Domain(X).1 select 1 else Degree(M_e[1]) :
        M_e in Conductor(X)] - 2;
  end if;
  return X`LDegree;
end intrinsic;

intrinsic RootNumber(X :: GrpDrchFFElt) -> FldCycElt
{ The global root number e(X) of a Dirichlet character X over k(t). }
  if not assigned X`RootNumber then
    X`RootNumber := EpsilonFactor(X) / SqrtResidueSize(X) ^ LDegree(X);
  end if;
  return X`RootNumber;
end intrinsic;

intrinsic LFunction(X :: GrpDrchFFElt : FunctionalEquation := false)
  -> RngUPolElt[FldCyc]
{ The formal L-function L(X, T) of a Dirichlet character X over k(t). If X has
  trivial conductor, then this is 1 / (1 - T) (1 - q T). Otherwise, if the
  FunctionalEquation L(X, T) = e(X) q^(d(X) / 2) T^(d(X)) L(X, 1 / q T)-bar is
  true, then the necessary computation may be decreased. By default,
  FunctionalEquation is set to be false. }
  if Conductor(X) eq [] then
    R<T> := PolynomialRing(Codomain(X));
    return 1 / ((1 - T) * (1 - ResidueSize(X) * T));
  end if;
  D := LDegree(X);
  return FunctionalEquation select
    LFunction(EulerFactors(X, Floor(D / 2)), D : FunctionalEquation := true,
      EpsilonFactor := EpsilonFactor(X), WeightFactor := 1 / ResidueSize(X),
      DualAutomorphism := ComplexConjugate)
    else LFunction(EulerFactors(X, D), D);
end intrinsic;