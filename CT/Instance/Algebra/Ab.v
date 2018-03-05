Require Import CT.Algebra.AbelianGroup.
Require Import CT.Category.

Set Universe Polymorphism.

(** * Ab: The category of abelian groups.

*)
Program Definition Ab (T : Type) : Category :=
  {| ob := @AbelianGroup T;
     mor := GroupHomomorphism;
     comp := fun _ _ _ => ab_group_hom_composition;
     id := fun _ => ab_group_hom_id;
     assoc := fun _ _ _ _ => ab_group_hom_composition_assoc
  |}.
Next Obligation.
Proof.
  symmetry.
  apply ab_group_hom_composition_assoc.
Qed.
Next Obligation.
Proof.
  apply ab_group_hom_eq.
  reflexivity.
Qed.
Next Obligation.
Proof.
  apply ab_group_hom_eq.
  reflexivity.
Qed.
