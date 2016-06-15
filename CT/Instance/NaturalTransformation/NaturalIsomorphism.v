Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Isomorphism.
Require Import CT.Instance.Category.FunctorCategory.

(** * Natural Isomorphism

Given the functor category {\(C\), \(D\)}, a _natural isomorphism_ is an
isomorphism between two objects of this category (i.e., functors between
\(C\) and \(D\)).
*)
Section NaturalIsomorphism.
  Context {C D : Category}.
  Context (F G : Functor C D).
  Definition NaturalIsomorphism := @Isomorphism (FunctorCategory C D) F G.
End NaturalIsomorphism.