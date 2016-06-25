Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Semigroup.
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


(* Possibly separate this out at some point. *)

(** * Monoid homomorphisms.

Magma homomorphisms that also preserve identity.
*)
Definition MonoidHomomorphism {A B} (M : @Monoid A) (N : @Monoid B) :=
  { f : @MagmaHomomorphism A B M N | magma_hom M N f (one M) = one N }.
