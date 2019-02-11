Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Isomorphism.
Require Import CT.Instance.Functor.ComposeFunctor.
Require Import CT.Instance.Functor.IdentityFunctor.
Require Import CT.Instance.NaturalTransformation.NaturalIsomorphism.
Require Import CT.Instance.NaturalTransformation.IdentityNaturalTransformation.

Record CategoryEquivalence (C D : Category) :=
  { F : Functor C D;
    G : Functor D C;
    ceq_nat_iso1 : NaturalIsomorphism (ComposeFunctor G F) (@IdentityFunctor D);
    ceq_nat_iso2 : NaturalIsomorphism (ComposeFunctor F G) (@IdentityFunctor C)
  }.