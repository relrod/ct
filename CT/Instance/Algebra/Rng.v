Require Import CT.Algebra.Rng.
Require Import CT.Category.

(** * Rngs form a category.

*)
Program Definition RngCategory (T : Type) : Category :=
  {| ob := @Rng T;
     mor := RngHomomorphism;
     comp := fun _ _ _ => rng_hom_composition;
     id := fun _ => rng_hom_id;
     assoc := fun _ _ _ _ => rng_hom_composition_assoc
  |}.
Next Obligation.
Proof.
  symmetry.
  apply rng_hom_composition_assoc.
Qed.
Next Obligation.
Proof. apply rng_hom_eq. reflexivity. Qed.
Next Obligation.
Proof. apply rng_hom_eq. reflexivity. Qed.
