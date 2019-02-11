Require Import CT.Category.
Require Import CT.Functor.
Require Export CT.Instance.Functor.Bifunctor.
Require Import CT.Instance.Functor.Endofunctor.

(** A product functor \(F\) on a category \(C\) is a [Bifunctor]:
\(F : C \times C \to C\). *)
Program Definition ProductFunctor (C : Category) := Bifunctor C C C.

(** This is just an alias for [ProductFunctor]. It is often used as a tensor
    product. *)
Definition Tensor := ProductFunctor.

(** The endofunctor \(- \otimes y\) for a given tensor functor \(t\) and
    given \(y \in Ob(C)\). *)
Program Definition _tensor {C : Category} (t : Tensor C) (y : @ob C)
  : Endofunctor C :=
  {| F_ob := fun a => F_ob t (a, y);
     F_mor := fun _ _ f => bimap f id
  |}.
Proof.
Next Obligation.
  unfold bimap.
  destruct t.
  simpl.
  rewrite F_id_law.
  trivial.
Qed.
Next Obligation.
  destruct t.
  simpl.
  rewrite <- F_comp_law.
  simpl.
  rewrite id_left.
  trivial.
Qed.

(** The endofunctor \(y \otimes -\) for a given tensor functor \(t\) and
    given \(y \in Ob(C)\). *)
Program Definition tensor_ {C : Category} (t : Tensor C) (y : @ob C)
  : Endofunctor C :=
  {| F_ob := fun a => F_ob t (y, a);
     F_mor := fun _ _ f => bimap id f
  |}.
Proof.
Next Obligation. apply _tensor_obligation_1. Qed.
Next Obligation.
  destruct t.
  simpl.
  rewrite <- F_comp_law.
  simpl.
  rewrite id_left.
  trivial.
Qed.

