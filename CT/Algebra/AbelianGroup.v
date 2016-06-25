Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.
Require Import CT.Algebra.Group.

(** * Abelian Groups

An abelian group is a group which is commutative.
*)
Record AbelianGroup {T : Type} :=
  { group :> @Group T;
    abelian_commutativity :
      forall x y,
        mu group x y = mu group y x
  }.