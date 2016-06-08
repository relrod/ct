Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.Functor.
Require Import CT.Instance.NaturalTransformation.

Program Definition FunctorCategory (C D : Category) : Category :=
  {| ob := Functor C D;
     mor := NaturalTransformation;
     id := IdentityNaturalTransformation;
     comp := @CompositionNaturalTransformation C D
  |}.
Next Obligation.
Proof.
  apply nt_eq.
  rewrite CompositionNaturalTransformation_assoc.
  reflexivity.
Qed.
Next Obligation.
Proof.
  rewrite CompositionNaturalTransformation_assoc.
  reflexivity.
Qed.
Next Obligation.
Proof. apply CompositionNaturalTransformation_id_left. Qed.
Next Obligation.
Proof. apply CompositionNaturalTransformation_id_right. Qed.

(* The category of endofunctors on some category. *)
Definition EndofunctorCategory (C : Category) := FunctorCategory C C.