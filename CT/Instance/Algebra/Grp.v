Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Group.
Require Import CT.Category.

Set Universe Polymorphism.

(** * Grp: The category of groups

*)
Program Definition Grp (T : Type) : Category :=
  {| ob := @Group T;
     mor := GroupHomomorphism;
     comp := fun _ _ _ => group_hom_composition;
     id := fun _ => group_hom_id;
     assoc := fun _ _ _ _ => group_hom_composition_assoc
  |}.
Next Obligation.
Proof.
  symmetry.
  apply group_hom_composition_assoc.
Qed.
Next Obligation.
Proof.
  apply group_hom_eq.
  reflexivity.
Qed.
Next Obligation.
Proof.
  apply group_hom_eq.
  reflexivity.
Qed.