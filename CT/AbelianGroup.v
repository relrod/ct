Require Import CT.Magma.
Require Import CT.Monoid.
Require Import CT.Semigroup.
Require Import CT.Group.

(** * Abelian Groups

An abelian group is a group which is commutative.
*)
Record AbelianGroup {T : Type} :=
  { group :> @Group T;
    abelian_commutativity :
      forall x y,
        mu group x y = mu group y x
  }.