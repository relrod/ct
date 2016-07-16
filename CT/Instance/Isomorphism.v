Require Import CT.Category.
Require Import CT.Isomorphism.

(** The identity isomorphism between objects. Each object in C is isomorphic to
itself, by definition. *)
Program Definition IdentityIso {C : Category} (a : @ob C) : Isomorphism a a :=
  {| to := id;
     from := id
  |}.
Next Obligation.
Proof.
  rewrite id_left. reflexivity.
Qed.
Next Obligation.
Proof.
  rewrite id_right. reflexivity.
Qed.

Program Definition InverseIso
        {C : Category}
        {a b : @ob C}
        (iso : Isomorphism a b) : Isomorphism b a :=
  {| to := from a b iso;
     from := to a b iso
  |}.
Next Obligation.
Proof.
  destruct iso.
  simpl.
  assumption.
Qed.
Next Obligation.
  destruct iso.
  simpl.
  assumption.
Qed.
