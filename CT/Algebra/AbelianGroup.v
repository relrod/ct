Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.
Require Export CT.Algebra.Group.

(** * Abelian Groups

An abelian group is a group which is commutative.
*)
Record AbelianGroup {T : Type} :=
  { group :> @Group T;
    abelian_commutativity :
      forall x y,
        mu group x y = mu group y x
  }.

(** * Composition of maps. *)
Program Definition ab_group_hom_composition
        {T U V : Type}
        {A : @AbelianGroup T}
        {B : @AbelianGroup U}
        {C : @AbelianGroup V}
        (map1 : GroupHomomorphism A B)
        (map2 : GroupHomomorphism B C) :
  GroupHomomorphism A C
  := magma_hom_composition map1 map2.

(** * Equality of maps, assuming proof irrelevance. *)
Program Definition ab_group_hom_eq
        {A B : Type}
        {F : @AbelianGroup A}
        {G : @AbelianGroup B}
        (N M : GroupHomomorphism F G) :
    @magma_hom A B F G N = @magma_hom A B F G M ->
    N = M
  := magma_hom_eq A B F G N M.

(** * Associativity of composition of maps. *)
Program Definition ab_group_hom_composition_assoc
        {T : Type}
        {A B C D : @AbelianGroup T}
        (f : GroupHomomorphism A B)
        (g : GroupHomomorphism B C)
        (h : GroupHomomorphism C D) :
  ab_group_hom_composition f (ab_group_hom_composition g h) =
  ab_group_hom_composition (ab_group_hom_composition f g) h
  := magma_hom_composition_assoc f g h.

(** * Identity map. *)
Program Definition ab_group_hom_id
        {A : Type}
        {M : @AbelianGroup A} :
  GroupHomomorphism M M :=
  magma_hom_id.