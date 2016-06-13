Require Import CT.Magma.
Require Import CT.Semigroup.
Require Import FunctionalExtensionality.

Set Primitive Projections.

Record Monoid {T : Type} :=
  { semigroup :> @Semigroup T;
    one : T;
    monoid_left_one : forall x, semigroup.(magma).(mu) one x = x;
    monoid_right_one : forall x, semigroup.(magma).(mu) x one = x
  }.

(** Monoid identity is unique. *)
Theorem monoid_identity_unique {T} {M : @Monoid T} e :
  (forall x, mu M x e = x) -> e = one M.
Proof.
  intros.
  destruct M.
  simpl in *.
  destruct (H e).
  rewrite <- (H one0).
  rewrite monoid_left_one0.
  trivial.
Qed.
