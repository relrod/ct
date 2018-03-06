Require Import Coq.Program.Tactics.
Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Semigroup.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Set Primitive Projections.

Record Monoid {T : Type} :=
  { semigroup :> @Semigroup T;
    one : T;
    monoid_left_one : forall x, semigroup.(magma).(mu) one x = x;
    monoid_right_one : forall x, semigroup.(magma).(mu) x one = x
  }.

Hint Resolve monoid_right_one.
Hint Resolve monoid_left_one.

Fixpoint mu_power {T : Type} (M : @Monoid T) (t : T) (n : nat) :=
  match n with
  | 0 => one M
  | S n => mu M t (mu_power M t n)
  end.

(** ** Monoid identity is unique. *)
Theorem monoid_identity_unique {T} {M : @Monoid T} e :
  (forall x, mu M x e = x) -> e = one M.
Proof.
  intros.
  destruct M.
  simpl in *.
  destruct (H e).
  rewrite <- (H one0).
  rewrite monoid_left_one0.
  trivial.
Qed.

Corollary monoid_identity_commutes {T} {M : @Monoid T} :
  forall a,
    mu M a (one M) = mu M (one M) a.
Proof.
  intros.
  rewrite monoid_left_one.
  rewrite monoid_right_one.
  trivial.
Qed.

(* Possibly separate this out at some point. *)

(** * Monoid homomorphisms.

Magma homomorphisms that also preserve identity.
*)
Record MonoidHomomorphism {A B} (M : @Monoid A) (N : @Monoid B) :=
  { monoid_hom :> @MagmaHomomorphism A B M N;
    monoid_hom_id_law : magma_hom M N monoid_hom (one M) = one N
  }.

(** * Composition of maps. *)
Program Definition monoid_hom_composition
        {T U V : Type}
        {A : @Monoid T}
        {B : @Monoid U}
        {C : @Monoid V}
        (map1 : MonoidHomomorphism A B)
        (map2 : MonoidHomomorphism B C) :
  MonoidHomomorphism A C :=
  {| monoid_hom :=
       {| magma_hom := fun a => (magma_hom B C map2) ((magma_hom A B map1) a)
       |}
  |}.
Next Obligation.
Proof.
  destruct A, B, C, map1, map2.
  simpl in *.
  rewrite magma_hom_law.
  rewrite magma_hom_law.
  trivial.
Qed.
Next Obligation.
  destruct A, B, C, map1, map2.
  simpl in *.
  rewrite monoid_hom_id_law0.
  rewrite monoid_hom_id_law1.
  trivial.
Qed.

(** * Equality of maps, assuming proof irrelevance. *)
Theorem monoid_hom_eq : forall A B F G (M N : MonoidHomomorphism F G),
    @monoid_hom A B F G M = @monoid_hom A B F G N ->
    M = N.
Proof.
  intros.
  destruct M, N.
  simpl in *.
  subst.
  f_equal.
  intros.
  rewrite H4.
  trivial.
  apply proof_irrelevance.
Qed.

(** * Associativity of composition of maps. *)
Program Definition monoid_hom_composition_assoc
        {T : Type}
        {A B C D : @Monoid T}
        (f : MonoidHomomorphism A B)
        (g : MonoidHomomorphism B C)
        (h : MonoidHomomorphism C D) :
  monoid_hom_composition f (monoid_hom_composition g h) =
  monoid_hom_composition (monoid_hom_composition f g) h.
Proof.
  destruct f, g, h.
  apply monoid_hom_eq.
  simpl.
  f_equal.
  intros.
  rewrite H4.
  trivial.
  apply proof_irrelevance.
  (* There's got to be a better way. *)
Qed.

(** * Identity map. *)
Program Definition monoid_hom_id
        {A : Type}
        {M : @Monoid A} :
  MonoidHomomorphism M M :=
  {| monoid_hom := {| magma_hom := fun a => a |} |}.