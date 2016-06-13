Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.FaithfulFunctor.
Require Import CT.Instance.Functor.FullFunctor.

(** * Fully Faithful Functors

A "fully faithful" functor is one that is both full and faithful.

We represent this simply as a pair of proofs of fullness and faithfulness.
*)
Section FullyFaithfulFunctor.
  Context {A B : Category}.
  Variable (F : Functor A B).

  Definition FullyFaithfulFunctor :=
    (FullFunctor F, FaithfulFunctor F).
End FullyFaithfulFunctor.