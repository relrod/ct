Set Primitive Projections.

Record Magma {T : Type} :=
  { mu : T -> T -> T
  }.

(* Possibly separate this out at some point. *)

(** * Magma homomorphisms.

Must obey this law:
\(f (a * b) = f(a) * f(b)\)
*)
Record MagmaHomomorphism {A B} (M : @Magma A) (N : @Magma B) :=
  { magma_hom : A -> B;
    magma_hom_law :
      forall (a b : A),
        magma_hom (mu M a b) = mu N (magma_hom a) (magma_hom b)
  }.