Require Import CT.Algebra.Magma.

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