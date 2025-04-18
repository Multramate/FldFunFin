/* L-FUNCTIONS OF DIRICHLET CHARACTERS OVER GLOBAL FUNCTION FIELDS

Let X be a Dirichlet character over a global function field K of a smooth proper
geometrically irreducible curve of genus g over a finite field k of order q,
with modulus a non-zero element M of k[t]. The motive [X] associated to X has
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
includes the type of Dirichlet characters and local Euler factors.
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
{ The Euler totient function Phi(M) over k(t) for a non-zero modulus M in k[t].
  This is the order of the unit group of k[t] / M. }
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

declare type GrpDrchFFElt;

declare attributes GrpDrchFFElt: Modulus, Generator, Image,
  BaseRing, Characteristic, Codomain, Domain, EulerPhi, Order,
  ResidueDegree, ResidueField, ResidueGenerator, ResidueSize,
  ResidueImage, ResidueCodomain, ResidueCharacter, ResidueOrder,
  IsEven, IsOdd, ResidueGaussSum, GaussSum, Conductor, LDegree, LFunction;

intrinsic DirichletCharacter(M :: RngUPolElt[FldFin], g :: Any, h :: FldCycElt :
    Minimal := false) -> GrpDrchFFElt
{ The Dirichlet character over k(t) of modulus a non-zero irreducible polynomial
  M of k[t], given by mapping an element g of k[t] that is a unit and a
  generator when reduced modulo M, to an element h in some cyclotomic field,
  which can be made Minimal. By default, Minimal is set to be false. }
  require IsIrreducible(M): "The modulus M is not a prime element of k[t].";
  require IsCoercible(Parent(M), g):
    "The generator g is not an element of k[t].";
  X := New(GrpDrchFFElt);
  X`Modulus := M;
  X`Generator := g;
  if Minimal then
    X`EulerPhi := EulerPhi(M);
    h := Minimise(CyclotomicField(X`EulerPhi) ! h);
  end if;
  X`Image := h;
  return X;
end intrinsic;

intrinsic DirichletCharacter(M :: RngUPolElt[FldFin], g :: Any,
    h :: FldRatElt : Minimal := false) -> GrpDrchFFElt
{ " }
  return DirichletCharacter(M, g, CyclotomicField(1) ! h : Minimal := Minimal);
end intrinsic;

intrinsic DirichletCharacter(M :: RngUPolElt[FldFin], g :: Any,
    h :: RngIntElt : Minimal := false) -> GrpDrchFFElt
{ " }
  return DirichletCharacter(M, g, CyclotomicField(1) ! h : Minimal := Minimal);
end intrinsic;

intrinsic DirichletCharacter(M :: FldFunRatUElt[FldFin], g :: Any,
    h :: FldCycElt : Minimal := false) -> GrpDrchFFElt
{ " }
  require Denominator(M) eq 1: "The modulus M is not an element of k[t].";
  return DirichletCharacter(Numerator(M), g, h : Minimal := Minimal);
end intrinsic;

intrinsic DirichletCharacter(M :: FldFunRatUElt[FldFin], g :: Any,
    h :: FldRatElt : Minimal := false) -> GrpDrchFFElt
{ " }
  return DirichletCharacter(M, g, CyclotomicField(1) ! h : Minimal := Minimal);
end intrinsic;

intrinsic DirichletCharacter(M :: FldFunRatUElt[FldFin], g :: Any,
    h :: RngIntElt : Minimal := false) -> GrpDrchFFElt
{ " }
  return DirichletCharacter(M, g, CyclotomicField(1) ! h : Minimal := Minimal);
end intrinsic;

intrinsic Modulus(X :: GrpDrchFFElt) -> RngUPolElt[FldFin]
{ The modulus of a Dirichlet character X over k(t). }
  return X`Modulus;
end intrinsic;

intrinsic Generator(X :: GrpDrchFFElt) -> RngUPolResElt[FldFin]
{ The generator that defines a Dirichlet character X over k(t). }
  return X`Generator;
end intrinsic;

intrinsic Image(X :: GrpDrchFFElt) -> FldCycElt
{ The image of the generator that defines a Dirichlet character X over k(t). }
  return X`Image;
end intrinsic;

intrinsic Minimise(X :: GrpDrchFFElt) -> GrpDrchFFElt
{ The same Dirichlet character X over k(t), but whose image of generator is
  coerced to its minimal cyclotomic field. }
  return DirichletCharacter(Modulus(X), Generator(X), Image(X) :
      Minimal := true);
end intrinsic;

intrinsic Minimise(~X :: GrpDrchFFElt)
{ " }
  X := Minimise(X);
end intrinsic;

intrinsic BaseRing(X :: GrpDrchFFElt) -> RngUPol[FldFin]
{ The base ring k[t] of a Dirichlet character X over k(t). }
  if not assigned X`BaseRing then
    X`BaseRing := Parent(Modulus(X));
  end if;
  return X`BaseRing;
end intrinsic;

intrinsic Characteristic(X :: GrpDrchFFElt) -> RngIntElt
{ The characteristic char(k(t)) of a Dirichlet character X over k(t). }
  if not assigned X`Characteristic then
    X`Characteristic := Characteristic(BaseRing(X));
  end if;
  return X`Characteristic;
end intrinsic;

intrinsic Codomain(X :: GrpDrchFFElt) -> FldCyc
{ The codomain of a Dirichlet character X over k(t). }
  if not assigned X`Codomain then
    X`Codomain := Parent(Image(X));
  end if;
  return X`Codomain;
end intrinsic;

intrinsic Domain(X :: GrpDrchFFElt) -> FldFunRat[FldFin]
{ The domain k(t) of a Dirichlet character X over k(t). }
  if not assigned X`Domain then
    X`Domain := FieldOfFractions(BaseRing(X));
  end if;
  return X`Domain;
end intrinsic;

intrinsic EulerPhi(X :: GrpDrchFFElt) -> RngIntElt
{ The Euler totient function Phi(M) of a Dirichlet character X over k(t) of a
  non-zero modulus M in k[t]. This is the order of the unit group of k[t] / M. }
  if not assigned X`EulerPhi then
    X`EulerPhi := EulerPhi(Modulus(X));
  end if;
  return X`EulerPhi;
end intrinsic;

intrinsic Order(X :: GrpDrchFFElt) -> RngIntElt
{ The order of a Dirichlet character X over k(t) in its character group. }
  if not assigned X`Order then
    X`Order := CyclotomicOrder(Codomain(Minimise(X)));
  end if;
  return X`Order;
end intrinsic;

intrinsic ResidueDegree(X :: GrpDrchFFElt) -> RngIntElt
{ The degree of the modulus of a Dirichlet character X over k(t). }
  if not assigned X`ResidueDegree then
    X`ResidueDegree := Degree(Modulus(X));
  end if;
  return X`ResidueDegree;
end intrinsic;

intrinsic ResidueField(X :: GrpDrchFFElt) -> FldFin
{ The residue field k of a Dirichlet character X over k(t). }
  if not assigned X`ResidueField then
    X`ResidueField := BaseRing(BaseRing(X));
  end if;
  return X`ResidueField;
end intrinsic;

intrinsic ResidueGenerator(X :: GrpDrchFFElt) -> FldFinElt
{ The generator of the residue field k of a Dirichlet character X over k(t) that
  defines the character over k associated to X. }
  if not assigned X`ResidueGenerator then
    X`ResidueGenerator := PrimitiveElement(ResidueField(X));
  end if;
  return X`ResidueGenerator;
end intrinsic;

intrinsic ResidueSize(X :: GrpDrchFFElt) -> RngIntElt
{ The size #k of the residue field k of a Dirichlet character X over k(t). }
  if not assigned X`ResidueSize then
    X`ResidueSize := #ResidueField(X);
  end if;
  return X`ResidueSize;
end intrinsic;

intrinsic Print(X :: GrpDrchFFElt)
{ The printing of a Dirichlet character X over k(t). }
  K<t> := Domain(X);
  printf
    "Dirichlet character over F_%o(%o) of modulus %o given by mapping %o to %o",
    ResidueSize(X), t, Modulus(X), K ! Generator(X), Image(X);
end intrinsic;

function Evaluate(X, x)
  M := Modulus(X);
  return BaseRing(X) ! x mod M eq 0 select 0 else
    Image(X) ^ Log(M, Generator(X), x);
end function;

intrinsic '@'(x :: Any, X :: GrpDrchFFElt) -> FldCycElt
{ The evaluation of a Dirichlet character X over k(t) on an element x of k[t]. }
  K<t> := Domain(X);
  require IsCoercible(K, x): "The element x is not an element of k(t).";
  x := K ! x;
  require Denominator(x) eq 1 or x eq 1 / t:
    "The element x is neither an element of k[t] nor 1 / t.";
  return x eq 1 / t select (IsEven(X) select 1 else 0) else Evaluate(X, x);
end intrinsic;

intrinsic ResidueImage(X :: GrpDrchFFElt) -> FldCycElt
{ The image of the generator of the residue field k of a Dirichlet character X
  over k(t) that defines the character over k associated to X. Note that this
  image is coerced to its minimal cyclotomic field. }
  if not assigned X`ResidueImage then
    X`ResidueImage := Minimise(X(ResidueGenerator(X)));
  end if;
  return X`ResidueImage;
end intrinsic;

intrinsic ResidueCodomain(X :: GrpDrchFFElt) -> FldCyc
{ The minimal codomain of the character over k associated to a Dirichlet
  character X over k(t). This is a subfield of the codomain of X. }
  if not assigned X`ResidueCodomain then
    X`ResidueCodomain := Parent(ResidueImage(X));
  end if;
  return X`ResidueCodomain;
end intrinsic;

intrinsic ResidueOrder(X :: GrpDrchFFElt) -> RngIntElt
{ The order of the character over k associated to a Dirichlet character X over
  k(t) in its character group. }
  if not assigned X`ResidueOrder then
    X`ResidueOrder := CyclotomicOrder(ResidueCodomain(X));
  end if;
  return X`ResidueOrder;
end intrinsic;

intrinsic ResidueCharacter(X :: GrpDrchFFElt) -> GrpDrchFFElt
{ The character over k associated to a Dirichlet character X over k(t). This
  is a Dirichlet character over k(t) of modulus t - 1, whose image of generator
  is coerced to its minimal cyclotomic field. }
  if not assigned X`ResidueCharacter then
    X`ResidueCharacter := DirichletCharacter(Domain(X).1 - 1,
        ResidueGenerator(X), ResidueImage(X));
  end if;
  return X`ResidueCharacter;
end intrinsic;

intrinsic IsEven(X :: GrpDrchFFElt) -> Bool
{ The parity of a Dirichlet character X over k(t). This returns true if X is
  even, namely that X is trivial on all elements of k. }
  if not assigned X`IsEven then
    X`IsEven := ResidueImage(X) eq 1;
  end if;
  return X`IsEven;
end intrinsic;

intrinsic IsOdd(X :: GrpDrchFFElt) -> Bool
{ The parity of a Dirichlet character X over k(t). This returns true if X is
  odd, namely that X is not trivial on some element of k. }
  if not assigned X`IsOdd then
    X`IsOdd := not IsEven(X);
  end if;
  return X`IsOdd;
end intrinsic;

function ResidueGaussSumFunc(X)
  C<z> := CyclotomicField(Characteristic(X));
  return &+[ResidueCharacter(X)(x) * z ^ IntegerRing() ! Trace(x) :
      x in ResidueField(X) | x ne 0];
end function;

intrinsic ResidueGaussSum(X :: GrpDrchFFElt) -> FldCycElt
{ The Gauss sum of the character over k associated to a Dirichlet character X
  over k(t) of characteristic p. This is the sum of X(x) of all non-zero
  elements x of k, weighted by p-th roots of unity raised to the trace of x. }
  if not assigned X`ResidueGaussSum then
    X`ResidueGaussSum := ResidueGaussSumFunc(X);
  end if;
  return X`ResidueGaussSum;
end intrinsic;

function GaussSumFunc(X)
  K<t> := Domain(X);
  D := Degree(Modulus(X)) - 1;
  return (IsEven(X) select -ResidueSize(X) else ResidueGaussSum(X))
    * &+[X(t ^ D + K ! s) : s in Subsequences(Set(ResidueField(X)), D)];
end function;

intrinsic GaussSum(X :: GrpDrchFFElt) -> FldCycElt
{ The Gauss sum of a Dirichlet character X over k(t) of a non-zero modulus M in
  k[t]. This is the sum of X(x) of all elements x of k[t] of degree at most the
  degree of M, weighted by the Hayes exponential function of x / M. }
  if not assigned X`GaussSum then
    X`GaussSum := GaussSumFunc(X);
  end if;
  return X`GaussSum;
end intrinsic;

function NormalisedGaussSumFunc(X)
  q_f := ResidueSize(X) ^ ResidueDegree(X);
  return ComplexField() ! GaussSum(X)
    / (Image(X) eq 1 select q_f else Sqrt(q_f));
end function;

intrinsic NormalisedGaussSum(X :: GrpDrchFFElt) -> FldComElt
{ The modulus of the Gauss sum of a Dirichlet character X over k(t). }
  return NormalisedGaussSumFunc(X);
end intrinsic;

function ConductorFunc(X)
  S := [];
  if IsOdd(X) then
    Append(~S, <1 / Domain(X).1, 1>);
  end if;
  if Image(X) ne 1 then
    Append(~S, <Modulus(X), 1>);
  end if;
  return S;
end function;

intrinsic Conductor(X :: GrpDrchFFElt) -> SeqEnum[Tup]
{ The conductor of a Dirichlet character X over k(t). This returns a sequence of
  tuples of the form <M, e>, where M is either a prime element of k[t] or 1 / t,
  and the local conductor exponent e at M is a positive integer. }
  if not assigned X`Conductor then
    X`Conductor := ConductorFunc(X);
  end if;
  return X`Conductor;
end intrinsic;

function EulerFactorFunc(X, v, D, P)
  R<T> := PolynomialRing(Codomain(X));
  if P lt D then
    return R ! 1;
  end if;
  return 1 - X(v) * T ^ D;
end function;

intrinsic EulerFactor(X :: GrpDrchFFElt, v :: Any : Exponent := 1,
    Precision := Infinity()) -> RngUPolElt
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
  return EulerFactorFunc(X, v, Exponent, Precision);
end intrinsic;

intrinsic EulerFactor(X :: GrpDrchFFElt : Exponent := 1,
    Precision := Infinity()) -> RngIntElt
{ The Euler factor L_v(X, T^D) of a Dirichlet character X over k(t) at
  v = 1 / t, where D is some Exponent. If Precision is set to be finite, then
  this is truncated to a polynomial of degree at most Precision. By default,
  Exponent is set to be 1 and Precision is set to be infinity. }
  return EulerFactor(X, 1 / Domain(X).1 : Exponent := 1,
      Precision := Precision);
end intrinsic;

function EulerFactorsFunc(X, D)
  k<a> := ResidueField(X);
  S := [PolynomialRing(Codomain(X)) | ];
  if D gt 0 then
    Append(~S, EulerFactorFunc(X, 1 / Domain(X).1, 1, D));
  end if;
  for i := 1 to D do
    for v in AllIrreduciblePolynomials(k, i) do
      Append(~S, EulerFactorFunc(X, v, Degree(v), D));
    end for;
  end for;
  return S;
end function;

intrinsic EulerFactors(X :: GrpDrchFFElt, D :: RngIntElt) -> SeqEnum[RngUPolElt]
{ The finite set of all Euler factors of a Dirichlet character X over k(t) at
  all places of k(t) of degree at most D. }
  requirege D, 0;
  return EulerFactorsFunc(X, D);
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

function LFunctionFunc(X)
  if Conductor(X) eq [] then
    R<T> := PolynomialRing(Codomain(X));
    return 1 / ((1 - T) * (1 - ResidueSize(X) * T));
  end if;
  D := LDegree(X);
  return LFunction(EulerFactors(X, D), D);
end function;

intrinsic LFunction(X :: GrpDrchFFElt : FunctionalEquation := false)
  -> RngUPolElt
{ The formal L-function L(X, T) of a Dirichlet character X over k(t). If X has
  trivial conductor, then this returns 1 / (1 - T) (1 - q T). Otherwise, if the
  FunctionalEquation L(X, T) = e(X) q^(d(X) / 2) T^(d(X)) L(X, 1 / q T) is true,
  then the necessary computation is decreased significantly. By default,
  FunctionalEquation is set to be false, since this has not been implemented. }
  require not FunctionalEquation:
    "The functional equation has not been implemented.";
  if not assigned X`LFunction then
    X`LFunction := LFunctionFunc(X);
  end if;
  return X`LFunction;
end intrinsic;