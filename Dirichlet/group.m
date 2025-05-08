/* GROUPS OF DIRICHLET CHARACTERS OVER GLOBAL FUNCTION FIELDS

Let R be the ring of integers of a global function field K of a smooth proper
geometrically irreducible curve over a finite field k. The group G of Dirichlet
characters over K of a non-zero modulus M in R is the dual of the unit group of
R / M. In other words, this is the group of group homomorphisms from the unit
group of R / M to the complex field, whose image lies in the cyclotomic
extension of K of modulus equal to the Euler totient function Phi(M) of M.

This file defines the group of Dirichlet characters of irreducible moduli over
the global function field k(t) of the projective line over a finite field k.
*/

declare type GrpDrchFF[GrpDrchFFElt];

declare attributes GrpDrchFF: Modulus, Generator,
  BaseRing, Characteristic, Domain, Size, Codomain,
  One, Characters, Group, Isomorphism,
  ResidueDegree, ResidueField, ResidueGenerator, ResidueSize, SqrtResidueSize;

intrinsic DirichletGroup(M :: RngUPolElt[FldFin] :
    Generator := MinimalGenerator(M)) -> GrpDrchFF
{ The group of Dirichlet characters over k(t) of modulus an irreducible
  polynomial M of k[t], given by mapping an element of k[t] that is a unit and a
  Generator when reduced modulo M, to elements in cyclotomic fields. By default,
  Generator is set to be the minimal generator of the unit group of k[t] / M. }
  require IsIrreducible(M): "The modulus M is not a prime element of k[t].";
  require IsCoercible(Parent(M), Generator):
    "The generator is not an element of k[t].";
  require IsGenerator(M, Generator):
    "The generator is not a generator of the unit group of k[t] / M.";
  G := New(GrpDrchFF);
  G`Modulus := M;
  G`Generator := Generator;
  return G;
end intrinsic;

intrinsic DirichletGroup(M :: FldFunRatUElt[FldFin] :
    Generator := MinimalGenerator(M)) -> GrpDrchFF
{ " }
  require Denominator(M) eq 1: "The modulus M is not an element of k[t].";
  return DirichletGroup(Numerator(M) : Generator := Generator);
end intrinsic;

intrinsic Modulus(G :: GrpDrchFF) -> RngUPolElt[FldFin]
{ The modulus of a group G of Dirichlet characters over k(t). }
  return G`Modulus;
end intrinsic;

intrinsic Generator(G :: GrpDrchFF) -> RngUPolElt[FldFin]
{ The generator of the unit group of k[t] / M that defines a group G of
  Dirichlet characters over k(t) of a non-zero modulus M in k[t]. }
  return G`Generator;
end intrinsic;

intrinsic ChangeGenerator(G :: GrpDrchFF, g :: Any) -> GrpDrchFFElt
{ The same group G of Dirichlet characters over k(t) of a non-zero modulus M in
  k[t] with generator changed to a generator g of the unit group of k[t] / M. }
  return DirichletGroup(Modulus(G) : Generator := g);
end intrinsic;

intrinsic ChangeGenerator(~G :: GrpDrchFF, g :: Any)
{ " }
  G := ChangeGenerator(G, g);
end intrinsic;

intrinsic BaseRing(G :: GrpDrchFF) -> RngUPol[FldFin]
{ The base ring k[t] for a group G of Dirichlet characters over k(t). }
  if not assigned G`BaseRing then
    G`BaseRing := Parent(Modulus(G));
  end if;
  return G`BaseRing;
end intrinsic;

intrinsic Characteristic(G :: GrpDrchFF) -> RngIntElt
{ The characteristic char(k) for a group G of Dirichlet characters over k(t). }
  if not assigned G`Characteristic then
    G`Characteristic := Characteristic(BaseRing(G));
  end if;
  return G`Characteristic;
end intrinsic;

intrinsic Domain(G :: GrpDrchFF) -> FldFunRat[FldFin]
{ The domain k(t) of a Dirichlet character in a group G of Dirichlet characters
  over k(t). This is the field of fractions of its base ring k[t]. }
  if not assigned G`Domain then
    G`Domain := FieldOfFractions(BaseRing(G));
  end if;
  return G`Domain;
end intrinsic;

intrinsic '#'(G :: GrpDrchFF) -> RngIntElt
{ The size of a group G of Dirichlet characters over k(t) of a non-zero modulus
  M in k[t]. This is the Euler totient function Phi(M) of M. }
  if not assigned G`Size then
    G`Size := EulerPhi(Modulus(G));
  end if;
  return G`Size;
end intrinsic;

intrinsic Codomain(G :: GrpDrchFF) -> FldCyc
{ The codomain of a Dirichlet character in a group G of Dirichlet characters
  over k(t). This is a cyclotomic field of modulus equal to the size of G. }
  if not assigned G`Codomain then
    G`Codomain := CyclotomicField(#G);
  end if;
  return G`Codomain;
end intrinsic;

intrinsic IsCoercible(G :: GrpDrchFF, X :: Any) -> BoolElt, Any
{ The coercion of X to a group G of Dirichlet characters over k(t). This is true
  if X is a Dirichlet character over k(t) in the finite set underlying G, in
  which case it returns X with generator changed to the generator of G, or if X
  is an element of some cyclotomic field equal to the image of the generator of
  some Dirichlet character over k(t) in G, in which case it returns a Dirichlet
  character over k(t) with generator equal to the generator of G and image X. }
  if Type(X) eq GrpDrchFFElt then
    bool := Characteristic(X) eq Characteristic(G) and Modulus(X) eq Modulus(G);
    return bool, bool select ChangeGenerator(X, Generator(G)) else
      "The modulus of G is different from the modulus of X.";
  else
    coercible, h := IsCoercible(Codomain(G), X);
    try
      return coercible, coercible select DirichletCharacter(G : Image := h) else
        "X is neither a Dirichlet character nor a cyclotomic element.";
    catch e
      return false, e`Object;
    end try;
  end if;
end intrinsic;

intrinsic 'in'(X :: Any, G :: GrpDrchFF) -> BoolElt
{ The membership of X in a group G of Dirichlet characters over k(t). This is
  true if X is a Dirichlet character over k(t) in the finite set underlying G or
  if X is an element of some cyclotomic field equal to the image of the
  generator of some Dirichlet character over k(t) in G. }
  return IsCoercible(G, X);
end intrinsic;

intrinsic One(G :: GrpDrchFF) -> GrpDrchFFElt
{ The identity of a group G of Dirichlet characters over k(t). }
  if not assigned G`One then
    G`One := G ! 1;
  end if;
  return G`One;
end intrinsic;

intrinsic Characters(G :: GrpDrchFF) -> SeqEnum[GrpDrchFFElt]
{ The finite set of Dirichlet characters over k(t) underlying a group G of
  Dirichlet characters over k(t). }
  if not assigned G`Characters then
    X := DirichletCharacter(G);
    G`Characters := [G | One(G)];
    for n := 1 to #G - 1 do
      G`Characters[n + 1] := G`Characters[n] * X;
    end for;
  end if;
  return G`Characters;
end intrinsic;

intrinsic Group(G :: GrpDrchFF) -> GrpAb, Map
{ The abstract additive abelian group A isomorphic to a group G of Dirichlet
  characters over k(t) and its associated isomorphism map from A to G. }
  if not assigned G`Group or not assigned G`Isomorphism then
    G`Group := AbelianGroup([#G]);
    characters := Characters(G);
    G`Isomorphism := hom<G`Group -> G | x :-> characters[Eltseq(x)[1] + 1],
        y :-> G`Group ! (Index(characters, y) - 1)>;
  end if;
  return G`Group, G`Isomorphism;
end intrinsic;

intrinsic ResidueDegree(G :: GrpDrchFF) -> RngIntElt
{ The residue degree for a group G of Dirichlet characters over k(t) of a
  non-zero modulus M in k[t]. This is equal to the degree deg(M) of M. }
  if not assigned G`ResidueDegree then
    G`ResidueDegree := Degree(Modulus(G));
  end if;
  return G`ResidueDegree;
end intrinsic;

intrinsic ResidueField(G :: GrpDrchFF) -> FldFin
{ The residue field k for a group G of Dirichlet characters over k(t). }
  if not assigned G`ResidueField then
    G`ResidueField := BaseRing(BaseRing(G));
  end if;
  return G`ResidueField;
end intrinsic;

intrinsic ResidueGenerator(G :: GrpDrchFF) -> FldFinElt
{ The generator of k for a group G of Dirichlet characters over k(t). }
  if not assigned G`ResidueGenerator then
    G`ResidueGenerator := PrimitiveElement(ResidueField(G));
  end if;
  return G`ResidueGenerator;
end intrinsic;

intrinsic ResidueSize(G :: GrpDrchFF) -> RngIntElt
{ The residue field size #k for a group G of Dirichlet characters over k(t). }
  if not assigned G`ResidueSize then
    G`ResidueSize := #ResidueField(G);
  end if;
  return G`ResidueSize;
end intrinsic;

intrinsic SqrtResidueSize(G :: GrpDrchFF) -> FldCycElt
{ The square root of #k for a group G of Dirichlet characters over k(t) as an
  element of its minimal cyclotomic field. }
  if not assigned G`SqrtResidueSize then
    q := ResidueSize(G);
    rad_q := Squarefree(q);
    G`SqrtResidueSize :=
      Sqrt(CyclotomicField(rad_q * (rad_q mod 4 eq 1 select 1 else 4)) ! q);
  end if;
  return G`SqrtResidueSize;
end intrinsic;

intrinsic Print(G :: GrpDrchFF)
{ The printing of a group G of Dirichlet characters over k(t). }
  K<t> := Domain(G);
  printf "Character group over F_%o(%o) of modulus %o with generator %o",
    ResidueSize(G), t, Modulus(G), K ! Generator(G);
end intrinsic;

intrinsic Random(G :: GrpDrchFF) -> GrpDrchFFElt
{ A random Dirichlet character over k(t) underlying a group G of Dirichlet
  characters over k(t). }
  return Random(Characters(G));
end intrinsic;