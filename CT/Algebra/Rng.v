Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.
Require Import CT.Algebra.Group.
Require Import CT.Algebra.AbelianGroup.

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
