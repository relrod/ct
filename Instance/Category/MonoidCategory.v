Require Import CT.Category.
Require Import CT.Monoid.

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
Proof. apply monoid_assoc. Qed.
Next Obligation.
Proof. rewrite <- monoid_assoc. reflexivity. Qed.
Next Obligation.
Proof. rewrite monoid_left_one. reflexivity. Qed.
Next Obligation.
Proof. rewrite monoid_right_one. reflexivity. Qed.
