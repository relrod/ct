Require Import CT.Category.
Require Import CT.Algebra.Group.
Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.

(** The category for a given group. A group is exactly a category with one
    object in which all morphisms are isomorphisms.
 *)
Program Definition GroupCategory {T} (G : Group) : Category :=
  {| ob := unit;
     mor := fun _ _ => T;
     comp := fun _ _ _ => mu G;
     id := fun a => one G;
  |}.
Next Obligation.
Proof. apply semigroup_assoc. Qed.
Next Obligation.
Proof.  symmetry. apply semigroup_assoc. Qed.
Next Obligation.
Proof. rewrite monoid_left_one. reflexivity. Qed.
Next Obligation.
Proof. rewrite monoid_right_one. reflexivity. Qed.

(* TODO: Prove that each morphism is an iso. *)