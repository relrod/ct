Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.

(** * Groups

A group is a monoid with inverses.
*)
Record Group {T : Type} :=
  { monoid :> @Monoid T;
    inverse : T -> T;
    gr_inverse_left : forall x : T, mu monoid (inverse x) x = one monoid;
    gr_inverse_right : forall x : T, mu monoid x (inverse x) = one monoid
  }.

Lemma group_unique_unop :
  forall {T} (G : @Group T) x y z,
    mu G x y = z -> x = mu G z (inverse G y).
  intros.
  rewrite <- H.
  rewrite <- semigroup_assoc.
  rewrite gr_inverse_right.
  rewrite monoid_right_one.
  reflexivity.
Qed.

(** This is given by [monoid_identity_unique] since a group is a monoid, but we
    prove it again in a different way, anyway. *)
Theorem group_identity_unique :
  forall {T} (G : @Group T) e x,
    mu G e x = x -> e = one G.
Proof.
  intros.
  rewrite (group_unique_unop G e x x).
  rewrite gr_inverse_right.
  reflexivity.
  assumption.
Qed.

Theorem group_inverse_inverse :
  forall {T} (G : @Group T) x,
    inverse G (inverse G x) = x.
Proof.
  intros.
  transitivity (mu G (inverse G (inverse G x)) (mu G (inverse G x) x)).
  rewrite gr_inverse_left.
  rewrite monoid_right_one.
  reflexivity.
  rewrite semigroup_assoc.
  rewrite gr_inverse_left.
  rewrite monoid_left_one.
  reflexivity.
Qed.

(* TODO: inverse unique, inverse over product, l/r cancellation,
   magma/semigroup/monoid/group homomorphisms + laws *)

(* Possibly separate this out at some point. *)

(** * Group homomorphisms.

...are exactly the same as magma homomorphisms.
*)
Definition GroupHomomorphism {A B} (M : @Group A) (N : @Group B) :=
  @MagmaHomomorphism A B M N.