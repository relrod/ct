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