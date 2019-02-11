Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Category.

(** * Mon: The category of monoids. *)
Program Definition Mon (T : Type) : Category :=
  {| ob := @Monoid T;
     mor := MonoidHomomorphism;
     comp := fun _ _ _ => monoid_hom_composition;
     id := fun _ => monoid_hom_id;
     assoc := fun _ _ _ _ => monoid_hom_composition_assoc
  |}.
Next Obligation.
Proof.
  symmetry.
  apply monoid_hom_composition_assoc.
Qed.
Next Obligation.
Proof.
  apply monoid_hom_eq.
  apply magma_hom_eq.
  reflexivity.
Qed.
Next Obligation.
Proof.
  apply monoid_hom_eq.
  apply magma_hom_eq.
  reflexivity.
Qed.