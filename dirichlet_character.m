/*
L-FUNCTIONS OF DIRICHLET CHARACTERS OVER GLOBAL FUNCTION FIELDS

This file defines some intrinsics for working with Dirichlet characters over the
global function field k(t) of the projective line over k, which has a unique
place at infinity 1 / t.
*/

declare type GrpDrchFFElt;

declare attributes GrpDrchFFElt: BaseRing, BaseField, Characteristic, Conductor,
  EulerPhi, Generator, GeneratorImage, ImageRing, Modulus, Parity, ResidueField,
  ResidueOrder, Variable;

intrinsic DirichletCharacter(M :: RngUPolElt[FldFin], g :: Any, h :: Any)
  -> GrpDrchFFElt
{ The Dirichlet character over k(t) of modulus a non-zero irreducible polynomial
  M in k[t], given by mapping an element g in k[t] that is a unit and a
  generator when reduced modulo M, to an element h that is a complex number. }
  R<t> := Parent(M);
  k<u> := BaseRing(R);
  require IsIrreducible(M): "The modulus M is not a prime element of k[t].";
  require IsCoercible(R, g): "The generator g is not a polynomial in k[t].";
  require IsCoercible(ComplexField(), h):
    "The element h is not a complex number.";
  X := New(GrpDrchFFElt);
  X`Generator := g;
  X`GeneratorImage := h;
  X`Modulus := M;
  return X;
end intrinsic;

intrinsic DirichletCharacter(M :: FldFunRatUElt[FldFin], g :: Any, h :: Any)
  -> GrpDrchFFElt
{ " }
  require Denominator(M) eq 1: "The modulus M is not a polynomial in k[t].";
  return DirichletCharacter(Numerator(M), g, h);
end intrinsic;

intrinsic BaseRing(X :: GrpDrchFFElt) -> RngUPol[FldFin]
{ The base ring k[t] of a Dirichlet character X over k(t). }
  if not assigned X`BaseRing then
    X`BaseRing := Parent(X`Modulus);
  end if;
  return X`BaseRing;
end intrinsic;

intrinsic BaseField(X :: GrpDrchFFElt) -> FldFunRat[FldFin]
{ The base field k(t) of a Dirichlet character X over k(t). }
  if not assigned X`BaseField then
    X`BaseField := FieldOfFractions(BaseRing(X));
  end if;
  return X`BaseField;
end intrinsic;

intrinsic Characteristic(X :: GrpDrchFFElt) -> RngIntElt
{ The characteristic char(k(t)) of a Dirichlet character X over k(t). }
  if not assigned X`Characteristic then
    X`Characteristic := Characteristic(BaseRing(X));
  end if;
  return X`Characteristic;
end intrinsic;

intrinsic Generator(X :: GrpDrchFFElt) -> RngUPolResElt[FldFin]
{ The generator that defines a Dirichlet character X over k(t). }
  return X`Generator;
end intrinsic;

intrinsic GeneratorImage(X :: GrpDrchFFElt) -> Any
{ The image of the generator that defines a Dirichlet character X over k(t). }
  return X`GeneratorImage;
end intrinsic;

intrinsic ImageRing(X :: GrpDrchFFElt) -> Any
{ The base ring of the codomain of a Dirichlet character X over k(t). }
  if not assigned X`ImageRing then
    X`ImageRing := Parent(X`GeneratorImage);
  end if;
  return X`ImageRing;
end intrinsic;

intrinsic Modulus(X :: GrpDrchFFElt) -> RngUPolElt[FldFin]
{ The modulus of a Dirichlet character X over k(t). }
  return X`Modulus;
end intrinsic;

intrinsic ResidueField(X :: GrpDrchFFElt) -> FldFin
{ The residue field k of a Dirichlet character X over k(t). }
  if not assigned X`ResidueField then
    X`ResidueField := BaseRing(BaseRing(X));
  end if;
  return X`ResidueField;
end intrinsic;

intrinsic ResidueOrder(X :: GrpDrchFFElt) -> RngIntElt
{ The residue order #k of a Dirichlet character X over k(t). }
  if not assigned X`ResidueOrder then
    X`ResidueOrder := #ResidueField(X);
  end if;
  return X`ResidueOrder;
end intrinsic;

intrinsic Variable(X :: GrpDrchFFElt) -> RngUPolElt
{ The variable t of a Dirichlet character X over k(t). }
  if not assigned X`Variable then
    X`Variable := BaseRing(X).1;
  end if;
  return X`Variable;
end intrinsic;

intrinsic Print(X :: GrpDrchFFElt)
{ Print a Dirichlet character X over k(t). }
  printf
    "Dirichlet character over F_%o(%o) of modulus %o given by mapping %o to %o",
    ResidueOrder(X), Variable(X), Modulus(X), Generator(X), GeneratorImage(X);
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

procedure AssignEulerPhi(X)
  X`EulerPhi := EulerPhi(Modulus(X));
end procedure;

intrinsic EulerPhi(X :: GrpDrchFFElt) -> RngIntElt
{ The Euler totient function Phi(M) of a Dirichlet character X over k(t) of a
  non-zero modulus M in k[t]. This is the order of the unit group of k[t] / M. }
  if not assigned X`EulerPhi then
    AssignEulerPhi(X);
  end if;
  return X`EulerPhi;
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
  require IsIrreducible(M): "The modulus M is not a prime element of k[t].";
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

function Evaluate(X, x)
  M := Modulus(X);
  return BaseRing(X) ! x mod M eq 0 select 0 else
    GeneratorImage(X) ^ Log(M, Generator(X), x);
end function;

intrinsic '@'(x :: Any, X :: GrpDrchFFElt) -> Any
{ Evaluate a Dirichlet character X over k(t) on an element x in k[t]. }
  require IsCoercible(BaseRing(X), x):
    "The element x is not a polynomial in k[t].";
  return Evaluate(X, x);
end intrinsic;

procedure AssignParity(X)
  X`Parity := X(PrimitiveRoot(ResidueOrder(X))) eq 1;
end procedure;

intrinsic Parity(X :: GrpDrchFFElt) -> Bool
{ The parity of a Dirichlet character X over k(t). This returns true if X is
  even, namely that X is trivial on all elements of k. }
  if not assigned X`Parity then
    AssignParity(X);
  end if;
  return X`Parity;
end intrinsic;

procedure AssignConductor(X)
  S := [];
  if not Parity(X) then
    Append(~S, <1 / Variable(X), 1>);
  end if;
  if GeneratorImage(X) ne 1 then
    Append(~S, <Modulus(X), 1>);
  end if;
  X`Conductor := S;
end procedure;

intrinsic Conductor(X :: GrpDrchFFElt) -> SeqEnum[Tup]
{ The conductor of a Dirichlet character X over k(t). This returns a sequence of
  tuples of the form <M, e>, where M is either a prime element of k[t] or 1 / t,
  and the local conductor exponent e at M is a positive integer. }
  if not assigned X`Conductor then
    AssignConductor(X);
  end if;
  return X`Conductor;
end intrinsic;

function EulerFactorFunc(X, v, D, P)
  R<T> := PolynomialRing(ImageRing(X));
  if P lt D then
    return R ! 1;
  end if;
  for pair in Conductor(X) do
    if BaseField(X) ! v eq pair[1] then
      return R ! 1;
    end if;
  end for;
  return 1 - (v eq 1 / Variable(X) select 1 / X(Variable(X)) else X(v)) * T ^ D;
end function;

intrinsic EulerFactor(X :: GrpDrchFFElt, v :: FldFunRatUElt[FldFin] :
    Exponent := Degree(v), Precision := Infinity()) -> RngUPolElt
{ The Euler factor L_v(X, T^D) of a Dirichlet character X over k(t) at a place v
  of k(t), which must either be a prime element of k[t] or 1 / t, where D is
  some Exponent. If Precision is set to be finite, then this is truncated to a
  polynomial of degree at most Precision, By default, Exponent is set to be the
  degree of the place associated to v and Precision is set to be infinity. }
  require Denominator(v) eq 1 or v eq 1 / Variable(X):
    "The place v is neither an element of k[t] nor 1 / t";
  requirege Exponent, 0;
  return EulerFactorFunc(X, v, Exponent, Precision);
end intrinsic;

intrinsic EulerFactor(X :: GrpDrchFFElt, v :: PlcFunElt : Exponent := Degree(v),
    Precision := Infinity()) -> RngUPolElt
{ The Euler factor L_v(X, T^D) of a Dirichlet character X over k(t) at a place v
  of k(t), where D is some Exponent. If Precision is set to be finite, then this
  is truncated to a polynomial of degree at most Precision. By default, Exponent
  is set to be the degree of v and Precision is set to be infinity. }
  return EulerFactor(X, BaseField(X) ! Minimum(v) : Exponent := Exponent,
      Precision := Precision);
end intrinsic;

intrinsic EulerFactor(X :: GrpDrchFFElt : Exponent := 1,
    Precision := Infinity()) -> RngIntElt
{ The Euler factor L_v(X, T^D) of a Dirichlet character X over k(t) at
  v = 1 / t, where D is some Exponent. If Precision is set to be finite, then
  this is truncated to a polynomial of degree at most Precision. By default,
  Exponent is set to be 1 and Precision is set to be infinity. }
  return EulerFactor(X, 1 / Variable(X) : Exponent := 1,
      Precision := Precision);
end intrinsic;

function EulerFactorsFunc(X, D)
  S := [PolynomialRing(ImageRing(X)) | ];
  if D gt 0 then
    Append(~S, EulerFactorFunc(X, 1 / Variable(X), 1, D));
  end if;
  for i := 1 to D do
    for v in AllIrreduciblePolynomials(ResidueField(X), i) do
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