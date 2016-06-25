Require Import CT.Magma.
Require Import CT.Monoid.
Require Import CT.Semigroup.
Require Import CT.Group.
Require Import CT.AbelianGroup.

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