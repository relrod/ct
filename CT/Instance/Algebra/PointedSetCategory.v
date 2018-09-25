Require Import CT.Algebra.PointedSet.
Require Import CT.Category.

(** * Pointed sets form a category.

The category is equivalent (but NOT isomorphic) to the category of sets with
partial functions. We do not prove this equivalence here (but probably should).
*)
Program Definition PointedSetCategory (T : Type) : Category :=
  {| ob := @PointedSet T;
     mor := PointPreservingMap;
     comp := fun _ _ _ => ppm_composition;
     id := fun _ => ppm_id;
     assoc := fun _ _ _ _ => ppm_composition_assoc
  |}.
Next Obligation.
Proof.
  symmetry.
  apply ppm_composition_assoc.
Qed.
Next Obligation.
Proof. apply ppm_eq. reflexivity. Qed.
Next Obligation.
Proof. apply ppm_eq. reflexivity. Qed.
