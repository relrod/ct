Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.
Require Import CT.Algebra.Group.
Require Import CT.Algebra.AbelianGroup.

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

Ring homomorphisms preserve identities and are homomorphisms for both the
group and monoid structures within the ring.

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
