Require Import CT.Algebra.Ring.
Require Import CT.Category.

Set Universe Polymorphism.

(** * Rings form a category.

*)
Program Definition RingCategory (T : Type) : Category :=
  {| ob := @Ring T;
     mor := RingHomomorphism;
     comp := fun _ _ _ => ring_hom_composition;
     id := fun _ => ring_hom_id;
     assoc := fun _ _ _ _ => ring_hom_composition_assoc
  |}.
Next Obligation.
Proof.
  symmetry.
  apply ring_hom_composition_assoc.
Qed.
Next Obligation.
Proof. apply ring_hom_eq. reflexivity. Qed.
Next Obligation.
Proof. apply ring_hom_eq. reflexivity. Qed.