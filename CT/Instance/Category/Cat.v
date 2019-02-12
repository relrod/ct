Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.

(** This is the category of Categories. :) *)
Program Definition Cat : Category :=
  {| ob := Category;
     mor := Functor;
     comp := @ComposeFunctor;
     id := @IdentityFunctor
  |}.
Next Obligation.
Proof. apply functor_comp_assoc. Qed.
Next Obligation.
Proof. symmetry. apply Cat_obligation_1. Qed.
Next Obligation.
Proof. apply comp_identity_left. trivial. Qed.
Next Obligation.
Proof. apply comp_identity_right. trivial. Qed.