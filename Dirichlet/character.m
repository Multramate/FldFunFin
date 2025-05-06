/* DIRICHLET CHARACTERS OVER GLOBAL FUNCTION FIELDS

Let R be the ring of integers of a global function field K of a smooth proper
geometrically irreducible curve over a finite field k. A Dirichlet character
over K of a non-zero modulus M in R is an element of its character group. In
other words, this is a group homomorphism from the unit group of R / M to the
complex field, whose image lies in the cyclotomic extension of K of modulus
equal to the Euler totient function Phi(M) of M.

This file defines Dirichlet characters of irreducible moduli over the global
function field k(t) of the projective line over a finite field k.
*/

declare type GrpDrchFFElt;

declare attributes GrpDrchFFElt: Parent, Image, Codomain, Order, Inverse,
  ResidueImage, ResidueCodomain, ResidueCharacter, ResidueOrder, IsEven, IsOdd,
  CharacterSum, EpsilonFactor, ResidueGaussSum, GaussSum,
  Conductor, LDegree, RootNumber;

intrinsic DirichletCharacter(M :: RngUPolElt[FldFin] :
    Generator := MinimalGenerator(M), Image) -> GrpDrchFFElt
{ The Dirichlet character over k(t) of modulus an irreducible polynomial M of
  k[t], given by mapping an element of k[t] that is a unit and a Generator when
  reduced modulo M, to an Image in some minimal cyclotomic field. By default,
  Generator is set to be the minimal generator of the unit group of k[t] / M,
  and Image is set to be the generator of the codomain of its character group. }
  require IsIrreducible(M): "The modulus M is not a prime element of k[t].";
  require IsCoercible(Parent(M), Generator):
    "The generator is not an element of k[t].";
  X := New(GrpDrchFFElt);
  X`Parent := DirichletGroup(M : Generator := Generator);
  C<z> := Codomain(X`Parent);
  coercible, h := IsCoercible(C, Image);
  X`Image := coercible select Minimise(h) else z;
  return X;
end intrinsic;

intrinsic DirichletCharacter(M :: FldFunRatUElt[FldFin] :
    Generator := MinimalGenerator(M), Image) -> GrpDrchFFElt
{ " }
  require Denominator(M) eq 1: "The modulus M is not an element of k[t].";
  return DirichletCharacter(Numerator(M) : Generator := Generator,
      Image := Image);
end intrinsic;

intrinsic Parent(X :: GrpDrchFFElt) -> GrpDrchFF
{ The character group of a Dirichlet character X over k(t). }
  return X`Parent;
end intrinsic;

intrinsic Image(X :: GrpDrchFFElt) -> FldCycElt
{ The image of the generator of the unit group of k[t] / M that defines a
  Dirichlet character over k(t) of a non-zero modulus M in k[t]. }
  return X`Image;
end intrinsic;

intrinsic Modulus(X :: GrpDrchFFElt) -> RngUPolElt[FldFin]
{ The modulus of a Dirichlet character X over k(t). }
  return Modulus(Parent(X));
end intrinsic;

intrinsic 'in'(X :: GrpDrchFFElt, G :: GrpDrchFF) -> BoolElt
{ The membership of a Dirichlet character X over k(t) in a group G of Dirichlet
  characters over k(t). This is true if the modulus of X is the modulus of G. }
  return Characteristic(X) eq Characteristic(G) and Modulus(X) eq Modulus(G);
end intrinsic;

intrinsic Generator(X :: GrpDrchFFElt) -> RngUPolElt[FldFin]
{ The generator of the unit group of k[t] / M that defines a Dirichlet character
  over k(t) of a non-zero modulus M in k[t]. }
  return Generator(Parent(X));
end intrinsic;

intrinsic ChangeGenerator(X :: GrpDrchFFElt, g :: Any) -> GrpDrchFFElt
{ The same Dirichlet character X over k(t) of a non-zero modulus M in k[t] with
  generator changed to a generator g of the unit group of k[t] / M. }
  return DirichletCharacter(Modulus(X) : Generator := g, Image := X(g));
end intrinsic;

intrinsic ChangeGenerator(~X :: GrpDrchFFElt, g :: Any)
{ " }
  X := ChangeGenerator(X, g);
end intrinsic;

intrinsic IsCoercible(G :: GrpDrchFF, X :: GrpDrchFFElt) -> BoolElt, Any
{ The coercion of a Dirichlet character X over k(t) to a group G of Dirichlet
  characters over k(t). This is true and returns X with generator changed to the
  generator of G if X is a member of G. }
  return X in G, X in G select ChangeGenerator(X, Generator(G)) else
    "The modulus of G is different from the modulus of X.";
end intrinsic;

intrinsic BaseRing(X :: GrpDrchFFElt) -> RngUPol[FldFin]
{ The base ring k[t] for a Dirichlet character X over k(t). }
  return BaseRing(Parent(X));
end intrinsic;

intrinsic Characteristic(X :: GrpDrchFFElt) -> RngIntElt
{ The characteristic char(k) for a Dirichlet character X over k(t). }
  return Characteristic(Parent(X));
end intrinsic;

intrinsic Domain(X :: GrpDrchFFElt) -> FldFunRat[FldFin]
{ The domain k(t) of a Dirichlet character X over k(t). }
  return Domain(Parent(X));
end intrinsic;

intrinsic ResidueDegree(X :: GrpDrchFFElt) -> RngIntElt
{ The residue degree for a Dirichlet character X over k(t) of a non-zero modulus
  M in k[t]. This is equal to the degree deg(M) of M. }
  return ResidueDegree(Parent(X));
end intrinsic;

intrinsic ResidueField(X :: GrpDrchFFElt) -> FldFin
{ The residue field k for a Dirichlet character X over k(t). }
  return ResidueField(Parent(X));
end intrinsic;

intrinsic ResidueGenerator(X :: GrpDrchFFElt) -> FldFinElt
{ The generator of k for a Dirichlet character X over k(t). }
  return ResidueGenerator(Parent(X));
end intrinsic;

intrinsic ResidueSize(X :: GrpDrchFFElt) -> RngIntElt
{ The residue field size #k for a Dirichlet character X over k(t). }
  return ResidueSize(Parent(X));
end intrinsic;

intrinsic SqrtResidueSize(X :: GrpDrchFFElt) -> FldCycElt
{ The square root of #k for a Dirichlet character X over k(t) as an element of
  its minimal cyclotomic field. }
  return SqrtResidueSize(Parent(X));
end intrinsic;

intrinsic Print(X :: GrpDrchFFElt)
{ The printing of a Dirichlet character X over k(t). }
  K<t> := Domain(X);
  printf
    "Dirichlet character over F_%o(%o) of modulus %o given by mapping %o to %o",
    ResidueSize(X), t, Modulus(X), K ! Generator(X), Image(X);
end intrinsic;

intrinsic Codomain(X :: GrpDrchFFElt) -> FldCyc
{ The minimal codomain of a Dirichlet character X over k(t). This is a subfield
  of the codomain of its character group. }
  if not assigned X`Codomain then
    X`Codomain := Parent(Image(X));
  end if;
  return X`Codomain;
end intrinsic;

intrinsic Order(X :: GrpDrchFFElt) -> RngIntElt
{ The order of a Dirichlet character X over k(t) in its character group. }
  if not assigned X`Order then
    X`Order := Conductor(Codomain(X));
  end if;
  return X`Order;
end intrinsic;

intrinsic '@'(x :: Any, X :: GrpDrchFFElt) -> FldCycElt
{ The evaluation of a Dirichlet character X over k(t) on an element x of k(t),
  which must either be an element of k[t] or 1 / t. }
  K<t> := Domain(X);
  require IsCoercible(K, x): "The element x is not an element of k(t).";
  x := K ! x;
  require Denominator(x) eq 1 or x eq 1 / t:
    "The element x is neither an element of k[t] nor 1 / t.";
  if x eq 1 / t then
    return IsEven(X) select 1 else 0;
  end if;
  M := Modulus(X);
  return BaseRing(X) ! x mod M eq 0 select 0 else
    Image(X) ^ Log(M, Generator(X), x);
end intrinsic;

intrinsic Inverse(X :: GrpDrchFFElt) -> GrpDrchFFElt
{ The inverse of a Dirichlet character X over k(t). This is also equal to the
  complex conjugate of X. }
  if not assigned X`Inverse then
    X`Inverse := DirichletCharacter(Modulus(X) : Generator := Generator(X),
        Image := 1 / Image(X));
  end if;
  return X`Inverse;
end intrinsic;

intrinsic 'eq'(X :: GrpDrchFFElt, Y :: GrpDrchFFElt) -> BoolElt
{ The equality of two Dirichlet characters X and Y over k(t). }
  coercible, Y := IsCoercible(Parent(X), Y);
  return coercible and Image(X) eq Image(Y);
end intrinsic;

intrinsic '^'(X :: GrpDrchFFElt, n :: RngIntElt) -> GrpDrchFFElt
{ The exponentiation of a Dirichlet character X over k(t) by an integer n. }
  return DirichletCharacter(Modulus(X) : Generator := Generator(X),
      Image := Image(X) ^ n);
end intrinsic;

intrinsic '*'(X :: GrpDrchFFElt, Y :: GrpDrchFFElt) -> GrpDrchFFElt
{ The multiplication of two Dirichlet characters X and Y over k(t). Note that
  this has not been implemented when X and Y have different moduli in k[t]. }
  coercible, Y := IsCoercible(Parent(X), Y);
  require coercible: "This has not been implemented for different moduli.";
  return DirichletCharacter(Modulus(X) : Generator := Generator(X),
      Image := Image(X) * Image(Y));
end intrinsic;

intrinsic '/'(X :: GrpDrchFFElt, Y :: GrpDrchFFElt) -> GrpDrchFFElt
{ The division of two Dirichlet characters X and Y over k(t). Note that this has
  not been implemented when X and Y have different moduli in k[t]. }
  return X * Inverse(Y);
end intrinsic;

intrinsic ResidueImage(X :: GrpDrchFFElt) -> FldCycElt
{ The image of the generator of k that defines the character over k associated
  to a Dirichlet character X over k(t). Note that this image is coerced to its
  minimal cyclotomic field. }
  if not assigned X`ResidueImage then
    X`ResidueImage := X(ResidueGenerator(X));
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

intrinsic ResidueCharacter(X :: GrpDrchFFElt) -> GrpDrchFFElt
{ The character over k associated to a Dirichlet character X over k(t). This is
  a Dirichlet character over k(t) of modulus t - 1, whose image of generator is
  coerced to its minimal cyclotomic field. }
  if not assigned X`ResidueCharacter then
    X`ResidueCharacter := DirichletCharacter(Domain(X).1 - 1 :
        Generator := ResidueGenerator(X), Image := ResidueImage(X));
  end if;
  return X`ResidueCharacter;
end intrinsic;

intrinsic ResidueOrder(X :: GrpDrchFFElt) -> RngIntElt
{ The order of the character over k associated to a Dirichlet character X over
  k(t) in its character group. }
  if not assigned X`ResidueOrder then
    X`ResidueOrder := Order(ResidueCharacter(X));
  end if;
  return X`ResidueOrder;
end intrinsic;

intrinsic IsEven(X :: GrpDrchFFElt) -> BoolElt
{ The parity of a Dirichlet character X over k(t). This is true if X is even,
  namely that X is trivial on all elements of k. }
  if not assigned X`IsEven then
    X`IsEven := ResidueImage(X) eq 1;
  end if;
  return X`IsEven;
end intrinsic;

intrinsic IsOdd(X :: GrpDrchFFElt) -> BoolElt
{ The parity of a Dirichlet character X over k(t). This is true if X is odd,
  namely that X is not trivial on some element of k. }
  if not assigned X`IsOdd then
    X`IsOdd := not IsEven(X);
  end if;
  return X`IsOdd;
end intrinsic;