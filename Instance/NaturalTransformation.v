Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.
Require Import FunctionalExtensionality.

Program Definition IdentityNaturalTransformation {A B : Category} (F : Functor A B) :
  NaturalTransformation F F :=
  {| nt_components := fun g => id
  |}.
Next Obligation.
Proof.
  rewrite id_left.
  rewrite id_right.
  reflexivity.
Qed.
Next Obligation.
Proof.
  rewrite id_left.
  rewrite id_right.
  reflexivity.
Qed.

Section CompositionNaturalTransformation.
  Context {C D : Category} {F G H : Functor C D}.
  Variable (N : NaturalTransformation F G) (O : NaturalTransformation G H).

  Program Definition CompositionNaturalTransformation : NaturalTransformation F H :=
    {| nt_components := fun g => comp (nt_components F G N g) (nt_components G H O g) |}.
  Next Obligation.
  Proof.
    rewrite assoc.
    rewrite nt_commutes.
    rewrite assoc_sym.
    rewrite assoc_sym.
    rewrite <- nt_commutes_sym.
    reflexivity.
  Qed.
  Next Obligation.
  Proof.
    symmetry.
    apply CompositionNaturalTransformation_obligation_1.
  Qed.
End CompositionNaturalTransformation.

(** Composition of natural transformations associates. *)
Theorem CompositionNaturalTransformation_assoc :
  forall C D F G H I
         (N : @NaturalTransformation C D H I)
         (O : @NaturalTransformation C D G H)
         (P : @NaturalTransformation C D F G),
           CompositionNaturalTransformation (CompositionNaturalTransformation P O) N =
           CompositionNaturalTransformation P (CompositionNaturalTransformation O N).
Proof.
  intros.
  apply nt_eq.
  simpl.
  extensionality g.
  rewrite assoc.
  reflexivity.
Qed.

(** The identity natural transformations acts as left compositional identity *)
Theorem CompositionNaturalTransformation_id_left :
  forall C D F G
         (N : @NaturalTransformation C D F G),
    CompositionNaturalTransformation (IdentityNaturalTransformation F) N = N.
Proof.
  intros.
  apply nt_eq.
  simpl.
  extensionality g.
  rewrite id_left.
  reflexivity.
Qed.

(** The identity natural transformations acts as right compositional identity *)
Theorem CompositionNaturalTransformation_id_right :
  forall C D F G
         (N : @NaturalTransformation C D F G),
    CompositionNaturalTransformation N (IdentityNaturalTransformation G) = N.
Proof.
  intros.
  apply nt_eq.
  simpl.
  extensionality g.
  rewrite id_right.
  reflexivity.
Qed.