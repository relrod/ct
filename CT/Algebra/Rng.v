Require Import Coq.Program.Tactics.
Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.
Require Import CT.Algebra.Group.
Require Import CT.Algebra.AbelianGroup.
Require Import ProofIrrelevance.

(** * Rngs (pseudo-rings)

A rng is an abelian group together with a semigroup whose multiplication is
distributive under group addition. *)
Record Rng {T : Type} :=
  { group :> @AbelianGroup T;
    semigroup :> @Semigroup T;
    semigroup_dist_over_group_l :
      forall a b c,
        mu semigroup a (mu group b c) =
        mu group (mu semigroup a b) (mu semigroup a c);
    semigroup_dist_over_group_r :
      forall a b c,
        mu semigroup (mu group b c) a =
        mu group (mu semigroup b a) (mu semigroup c a)
  }.

(* Possibly separate this out at some point. *)

(** * Rng homomorphisms.

Rng homomorphisms are homomorphisms for both the group and monoid structures
within the ring.

It would be nice to piggyback off of [MagmaHomomorphism] some day, but this
seems difficult(?).
*)
Record RngHomomorphism {A B} (M : @Rng A) (N : @Rng B) :=
  { rng_hom : A -> B;
    rng_monoid_hom_law :
      forall (a b : A),
        rng_hom (mu (monoid M) a b) =
        mu (monoid N) (rng_hom a) (rng_hom b);
    rng_group_hom_law :
      forall (a b : A),
        rng_hom (mu (group M) a b) =
        mu (group N) (rng_hom a) (rng_hom b)
  }.

(** * Composition of maps. *)
Program Definition rng_hom_composition
        {T U V : Type}
        {A : @Rng T}
        {B : @Rng U}
        {C : @Rng V}
        (map1 : RngHomomorphism A B)
        (map2 : RngHomomorphism B C) :
  RngHomomorphism A C :=
  {| rng_hom := fun a => (rng_hom B C map2) ((rng_hom A B map1) a) |}.
Next Obligation.
Proof.
  destruct A, B, C, map1, map2.
  simpl in *.
  rewrite rng_monoid_hom_law0.
  rewrite rng_monoid_hom_law1.
  trivial.
Qed.
Next Obligation.
Proof.
  destruct A, B, C, map1, map2.
  simpl in *.
  rewrite rng_group_hom_law0.
  rewrite rng_group_hom_law1.
  trivial.
Qed.

(** * Equality of maps, assuming proof irrelevance. *)
Theorem rng_hom_eq : forall A B F G (N M : RngHomomorphism F G),
    @rng_hom A B F G N = @rng_hom A B F G M ->
    N = M.
Proof.
  intros.
  destruct N, M.
  simpl in *.
  subst.
  f_equal.
  intros.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

(** * Associativity of composition of maps. *)
Program Definition rng_hom_composition_assoc
        {T : Type}
        {A B C D : @Rng T}
        (f : RngHomomorphism A B)
        (g : RngHomomorphism B C)
        (h : RngHomomorphism C D) :
  rng_hom_composition f (rng_hom_composition g h) =
  rng_hom_composition (rng_hom_composition f g) h.
Proof.
  destruct f, g, h.
  apply rng_hom_eq.
  simpl.
  reflexivity.
Qed.

(** * Identity map. *)
Program Definition rng_hom_id
        {A : Type}
        {M : @Rng A} :
  RngHomomorphism M M :=
  {| rng_hom := fun a => a |}.