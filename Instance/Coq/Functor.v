Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Coq.Category.
Require Import CT.Instance.Functor.Endofunctor.
Require Import FunctionalExtensionality List.

(** List functor. Just for grins. :) *)
Program Definition CoqListFunctor : @Endofunctor CoqType :=
  {| F_ob := list : @ob CoqType -> @ob CoqType;
     F_mor := map
  |}.
Next Obligation.
Proof.
  extensionality x.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.
Next Obligation.
  extensionality x.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

(** Option functor. Just for grins. :) *)
Program Definition CoqOptionFunctor : @Endofunctor CoqType :=
  {| F_ob := option : @ob CoqType -> @ob CoqType;
     F_mor := option_map
  |}.
Next Obligation.
Proof.
  extensionality x.
  destruct x.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
Next Obligation.
Proof.
  extensionality x.
  destruct x.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
