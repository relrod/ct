Require Import CT.Magma.
Require Import CT.Monoid.
Require Import CT.Semigroup.

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

(* TODO: inverse unique, double inverse, inverse over product, l/r cancellation,
   magma/semigroup/monoid/group homomorphisms + laws *)