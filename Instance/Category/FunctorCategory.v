Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.Functor.
Require Import CT.Instance.NaturalTransformation.

Program Definition FunctorCategory (C D : Category) : Category :=
  {| ob := Functor C D;
     mor := NaturalTransformation;
     id := IdentityNaturalTransformation;
     comp := @VCNaturalTransformation C D
  |}.
Next Obligation.
Proof.
  apply nt_eq.
  rewrite VCNaturalTransformation_assoc.
  reflexivity.
Qed.
Next Obligation.
Proof.
  rewrite VCNaturalTransformation_assoc.
  reflexivity.
Qed.
Next Obligation.
Proof. apply VCNaturalTransformation_id_left. Qed.
Next Obligation.
Proof. apply VCNaturalTransformation_id_right. Qed.

(* The category of endofunctors on some category. *)
Definition EndofunctorCategory (C : Category) := FunctorCategory C C.