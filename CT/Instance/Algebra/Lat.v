Require Import CT.Algebra.Lattice.
Require Import CT.Category.
Require Import CT.Order.PartiallyOrderedSet.
Require Import Coq.Program.Tactics.

(** * Lat: The category of lattices.
*)
Program Definition Lat : Category :=
  {| ob := Lattice;
     mor := LatticeHomomorphism;
     comp := fun _ _ _ => lattice_hom_composition;
     id := fun _ => lattice_hom_id;
     assoc := fun _ _ _ _ => lattice_hom_composition_assoc
  |}.
Next Obligation.
Proof.
  symmetry.
  apply lattice_hom_composition_assoc.
Qed.
Next Obligation.
Proof. apply lattice_hom_eq. reflexivity. Qed.
Next Obligation.
Proof. apply lattice_hom_eq. reflexivity. Qed.

