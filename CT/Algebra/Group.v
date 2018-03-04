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

Theorem group_identity_unique {T} (G : @Group T) e :
  (forall x, mu G x e = x) -> e = one G.
Proof.
  apply (monoid_identity_unique e).
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

(**
Uniqueness of inverses. This proof is basically a replica of Dummit and Foote.
*)
Theorem group_inverse_unique {T} (G : @Group T) c :
  forall a,
    mu G a c = one G ->
    mu G c a = one G ->
    inverse G a = c.
Proof.
  intros.
  assert (c = mu G c (one G)).
  rewrite monoid_right_one.
  trivial.
  assert (one G = mu G a (inverse G a)).
  rewrite gr_inverse_right.
  trivial.
  rewrite H2 in H1.
  rewrite semigroup_assoc in H1.
  rewrite H0 in H1.
  rewrite H1.
  rewrite monoid_left_one.
  trivial.
Qed.

(** Inverses over products.

This gives an ugly proof of \((ab^{-1}) = b^{-1}a^{-1}\).
*)
Theorem group_inverse_of_product {T} (G : @Group T) :
  forall a b,
    inverse G (mu G a b) = mu G (inverse G b) (inverse G a).
Proof.
  intros.
  assert (mu G (mu G a b) (inverse G (mu G a b)) = one G).
  apply gr_inverse_right.
  assert (mu G (mu G a b) (mu G (inverse G b) (inverse G a)) = one G).
  assert (mu G (mu G a b) (mu G (inverse G b) (inverse G a)) =
          mu G (mu G a (mu G b (inverse G b))) (inverse G a)).
  rewrite semigroup_assoc.
  rewrite semigroup_assoc.
  trivial.
  rewrite H0.
  rewrite gr_inverse_right.
  rewrite monoid_right_one.
  apply gr_inverse_right.
  rewrite <- (group_inverse_unique G (mu G a b) (mu G (inverse G b) (inverse G a))).
  rewrite group_inverse_inverse.
  trivial.
  rewrite semigroup_assoc.
  assert (mu G (mu G (mu G (inverse G b) (inverse G a)) a) b =
          mu G (mu G (inverse G b) (mu G (inverse G a) a)) b).
  rewrite semigroup_assoc.
  trivial.
  rewrite H1.
  rewrite gr_inverse_left.
  rewrite monoid_right_one.
  apply gr_inverse_left.
  assumption.
Qed.

(* TODO: l/r cancellation,
   magma/semigroup/monoid/group homomorphisms + laws *)

(* Possibly separate this out at some point. *)

(** * Group homomorphisms.

...are exactly the same as magma homomorphisms.
*)
Definition GroupHomomorphism {A B} (M : @Group A) (N : @Group B) :=
  @MagmaHomomorphism A B M N.