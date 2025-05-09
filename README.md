# Motives over global function fields in Magma

This repository implements some intrinsics in the Magma computer algebra system
for working with explicit motives over global function fields.

This includes a raw implementation of Dirichlet characters and their character
groups, consisting of the following files.

- [General intrinsics](Dirichlet/general.m)
- [Character groups](Dirichlet/group.m)
- [Dirichlet characters](Dirichlet/character.m)

This also includes a computation of L-functions of the motives associated to
Dirichlet twists of elliptic curves, consisting of the following files.

- [General intrinsics](LFunction/general.m)
- [Dirichlet characters](LFunction/dirichlet_character.m)
- [Elliptic curves](LFunction/elliptic_curve.m)
- [Dirichlet twists](LFunction/tensor_product.m)

The first edition of this repository completed by May 2025 is a minimum viable
product, with features limited by the following constraints.

- The curve underlying the global function field is assumed to be the projective
line over a finite field with a unique place at infinity
- The moduli underlying Dirichlet characters are assumed to be irreducible
- The local root numbers and functional equations of elliptic curves have only
been implemented for characteristics greater than 3
- The local conductor exponents of elliptic curves and Dirichlet characters in
Dirichlet twists are assumed to have disjoint support

This repository will be continuously developed over time, to remove these
assumptions as well as to implement new motives, such as Artin representations
and hyperelliptic curves, but external assistance is highly welcome.

The code should be used at your own risk, and any mistakes in it are of my own.