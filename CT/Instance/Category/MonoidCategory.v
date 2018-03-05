Require Import CT.Category.
Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.

(** The category for a given monoid. A monoid is exactly a category with one
    object.
 *)
Program Definition MonoidCategory {T} (M : Monoid) : Category :=
  {| ob := unit;
     mor := fun _ _ => T;
     comp := fun _ _ _ => mu M;
     id := fun a => one M;
  |}.
Next Obligation.
Proof. apply semigroup_assoc. Qed.
Next Obligation.
Proof.  symmetry. apply semigroup_assoc. Qed.
Next Obligation.
Proof. rewrite monoid_left_one. reflexivity. Qed.
Next Obligation.
Proof. rewrite monoid_right_one. reflexivity. Qed.