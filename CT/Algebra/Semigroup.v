Require Import Coq.Program.Tactics.
Require Import CT.Algebra.Magma.
Require Import ProofIrrelevance.

Set Primitive Projections.

Record Semigroup {T : Type} :=
  { magma :> @Magma T;
    semigroup_assoc : forall x y z, magma.(mu) x (magma.(mu) y z) = magma.(mu) (magma.(mu) x y) z
  }.

(* Possibly separate this out at some point. *)

(** * Semigroup homomorphisms.

...are exactly the same as magma homomorphisms.
*)
Definition SemigroupHomomorphism {A B} (M : @Semigroup A) (N : @Semigroup B) :=
  @MagmaHomomorphism A B M N.

(** * Composition of maps. *)
Program Definition semigroup_hom_composition
        {T U V : Type}
        {A : @Semigroup T}
        {B : @Semigroup U}
        {C : @Semigroup V}
        (map1 : SemigroupHomomorphism A B)
        (map2 : SemigroupHomomorphism B C) :
  SemigroupHomomorphism A C
  := magma_hom_composition map1 map2.

(** * Equality of maps, assuming proof irrelevance. *)
Program Definition semigroup_hom_eq
        {A B : Type}
        {F : @Semigroup A}
        {G : @Semigroup B}
        (N M : SemigroupHomomorphism F G) :
    @magma_hom A B F G N = @magma_hom A B F G M ->
    N = M
  := magma_hom_eq A B F G N M.

(** * Associativity of composition of maps. *)
Program Definition semigroup_hom_composition_assoc
        {T : Type}
        {A B C D : @Semigroup T}
        (f : SemigroupHomomorphism A B)
        (g : SemigroupHomomorphism B C)
        (h : SemigroupHomomorphism C D) :
  semigroup_hom_composition f (semigroup_hom_composition g h) =
  semigroup_hom_composition (semigroup_hom_composition f g) h
  := magma_hom_composition_assoc f g h.

(** * Identity map. *)
Program Definition semigroup_hom_id
        {A : Type}
        {M : @Semigroup A} :
  SemigroupHomomorphism M M :=
  magma_hom_id.