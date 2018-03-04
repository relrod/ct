Require Import Coq.Program.Tactics.
Require Import ProofIrrelevance.

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

(** * Composition of maps. *)
Program Definition magma_hom_composition
        {T U V : Type}
        {A : @Magma T}
        {B : @Magma U}
        {C : @Magma V}
        (map1 : MagmaHomomorphism A B)
        (map2 : MagmaHomomorphism B C) :
  MagmaHomomorphism A C :=
  {| magma_hom := fun a => (magma_hom B C map2) ((magma_hom A B map1) a) |}.
Next Obligation.
Proof.
  destruct A, B, C, map1, map2.
  simpl in *.
  rewrite magma_hom_law0.
  rewrite magma_hom_law1.
  trivial.
Qed.

(** * Equality of maps, assuming proof irrelevance. *)
Theorem magma_hom_eq : forall A B F G (N M : MagmaHomomorphism F G),
    @magma_hom A B F G N = @magma_hom A B F G M ->
    N = M.
Proof.
  intros.
  destruct N, M.
  simpl in *.
  subst.
  f_equal.
  intros.
  apply proof_irrelevance.
Qed.

(** * Associativity of composition of maps. *)
Program Definition magma_hom_composition_assoc
        {T : Type}
        {A B C D : @Magma T}
        (f : MagmaHomomorphism A B)
        (g : MagmaHomomorphism B C)
        (h : MagmaHomomorphism C D) :
  magma_hom_composition f (magma_hom_composition g h) =
  magma_hom_composition (magma_hom_composition f g) h.
Proof.
  destruct f, g, h.
  apply magma_hom_eq.
  simpl.
  reflexivity.
Qed.

(** * Identity map. *)
Program Definition magma_hom_id
        {A : Type}
        {M : @Magma A} :
  MagmaHomomorphism M M :=
  {| magma_hom := fun a => a |}.