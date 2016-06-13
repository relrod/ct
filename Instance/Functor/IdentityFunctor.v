Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.Endofunctor.
Require Import CT.Instance.Functor.FaithfulFunctor.

Program Definition IdentityFunctor {C : Category} : @Endofunctor C :=
  {| F_ob := fun x => x;
     F_mor := fun _ _ f => f;
  |}.

(** The identity functor is always faithful. *)
Theorem identity_is_faithful (C : Category) : FaithfulFunctor (@IdentityFunctor C).
Proof.
  intro.
  simpl.
  trivial.
Qed.
