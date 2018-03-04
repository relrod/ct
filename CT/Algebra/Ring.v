Require Import Coq.Program.Tactics.
Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.
Require Import CT.Algebra.Group.
Require Import CT.Algebra.AbelianGroup.
Require Import ProofIrrelevance.

(** * Rings

A ring is an abelian group together with a monoid whose multiplication is
distributive under group addition. *)
Record Ring {T : Type} :=
  { group :> @AbelianGroup T;
    monoid :> @Monoid T;
    monoid_dist_over_group_l :
      forall a b c,
        mu monoid a (mu group b c) = mu group (mu monoid a b) (mu monoid a c);
    monoid_dist_over_group_r :
      forall a b c,
        mu monoid (mu group b c) a = mu group (mu monoid b a) (mu monoid c a)
  }.

(* Possibly separate this out at some point. *)

(** * Ring homomorphisms.

Ring homomorphisms preserve multiplicative identities and are homomorphisms for
both the group and monoid structures within the ring.

It would be nice to piggyback off of [MagmaHomomorphism] some day, but this
seems difficult(?).
*)
Record RingHomomorphism {A B} (M : @Ring A) (N : @Ring B) :=
  { ring_hom : A -> B;
    ring_monoid_hom_law :
      forall (a b : A),
        ring_hom (mu (monoid M) a b) =
        mu (monoid N) (ring_hom a) (ring_hom b);
    ring_group_hom_law :
      forall (a b : A),
        ring_hom (mu (group M) a b) =
        mu (group N) (ring_hom a) (ring_hom b);
    ring_id_hom_law :
      ring_hom (one (monoid M)) = one (monoid N)
  }.

(** * Composition of maps. *)
Program Definition ring_hom_composition
        {T U V : Type}
        {A : @Ring T}
        {B : @Ring U}
        {C : @Ring V}
        (map1 : RingHomomorphism A B)
        (map2 : RingHomomorphism B C) :
  RingHomomorphism A C :=
  {| ring_hom := fun a => (ring_hom B C map2) ((ring_hom A B map1) a) |}.
Next Obligation.
Proof.
  destruct A, B, C, map1, map2.
  simpl in *.
  rewrite ring_monoid_hom_law0.
  rewrite ring_monoid_hom_law1.
  trivial.
Qed.
Next Obligation.
Proof.
  destruct A, B, C, map1, map2.
  simpl in *.
  rewrite ring_group_hom_law0.
  rewrite ring_group_hom_law1.
  trivial.
Qed.
Next Obligation.
Proof.
  destruct A, B, C, map1, map2.
  simpl in *.
  rewrite ring_id_hom_law0.
  assumption.
Qed.

(** * Equality of maps, assuming proof irrelevance. *)
Theorem ring_hom_eq : forall A B F G (N M : RingHomomorphism F G),
    @ring_hom A B F G N = @ring_hom A B F G M ->
    N = M.
Proof.
  intros.
  destruct N, M.
  simpl in *.
  subst.
  f_equal.
  intros.
  rewrite H4.
  rewrite H5.
  rewrite H6.
  trivial.
  apply proof_irrelevance.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

(** * Associativity of composition of maps. *)
Program Definition ring_hom_composition_assoc
        {T : Type}
        {A B C D : @Ring T}
        (f : RingHomomorphism A B)
        (g : RingHomomorphism B C)
        (h : RingHomomorphism C D) :
  ring_hom_composition f (ring_hom_composition g h) =
  ring_hom_composition (ring_hom_composition f g) h.
Proof.
  destruct f, g, h.
  apply ring_hom_eq.
  simpl.
  reflexivity.
Qed.

(** * Identity map. *)
Program Definition ring_hom_id
        {A : Type}
        {M : @Ring A} :
  RingHomomorphism M M :=
  {| ring_hom := fun a => a |}.