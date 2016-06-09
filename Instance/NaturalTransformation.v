Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.Functor.
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

Section VerticalCompositionNaturalTransformation.
  Context {C D : Category} {F G H : Functor C D}.
  Variable (N : NaturalTransformation F G) (O : NaturalTransformation G H).

  Program Definition VerticalCompositionNaturalTransformation : NaturalTransformation F H :=
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
    apply VerticalCompositionNaturalTransformation_obligation_1.
  Qed.
End VerticalCompositionNaturalTransformation.

(** Composition of natural transformations associates. *)
Theorem VerticalCompositionNaturalTransformation_assoc :
  forall C D F G H I
         (N : @NaturalTransformation C D H I)
         (O : @NaturalTransformation C D G H)
         (P : @NaturalTransformation C D F G),
           VerticalCompositionNaturalTransformation (VerticalCompositionNaturalTransformation P O) N =
           VerticalCompositionNaturalTransformation P (VerticalCompositionNaturalTransformation O N).
Proof.
  intros.
  apply nt_eq.
  simpl.
  extensionality g.
  rewrite assoc.
  reflexivity.
Qed.

(** The identity natural transformations acts as left compositional identity *)
Theorem VerticalCompositionNaturalTransformation_id_left :
  forall C D F G
         (N : @NaturalTransformation C D F G),
    VerticalCompositionNaturalTransformation (IdentityNaturalTransformation F) N = N.
Proof.
  intros.
  apply nt_eq.
  simpl.
  extensionality g.
  rewrite id_left.
  reflexivity.
Qed.

(** The identity natural transformations acts as right compositional identity *)
Theorem VerticalCompositionNaturalTransformation_id_right :
  forall C D F G
         (N : @NaturalTransformation C D F G),
    VerticalCompositionNaturalTransformation N (IdentityNaturalTransformation G) = N.
Proof.
  intros.
  apply nt_eq.
  simpl.
  extensionality g.
  rewrite id_right.
  reflexivity.
Qed.

Section HorizontalCompositionNaturalTransformation.
  Context {C D E : Category} {F G : Functor C D} {J K : Functor D E}.
  Variable (N : NaturalTransformation F G) (O : NaturalTransformation J K).

  Program Definition HorizontalCompositionNaturalTransformation : NaturalTransformation (ComposeFunctor F J) (ComposeFunctor G K) :=
    {| nt_components :=
         fun g => comp (nt_components J K O (F_ob F g)) (F_mor K (nt_components F G N g)) |}.
  Next Obligation.
  Proof.
    rewrite assoc.
    rewrite nt_commutes.
    rewrite assoc_sym.
    rewrite <- F_comp_law.
    rewrite nt_commutes.
    rewrite F_comp_law.
    rewrite assoc.
    reflexivity.
  Qed.
  Next Obligation.
  Proof.
    symmetry.
    apply HorizontalCompositionNaturalTransformation_obligation_1.
  Qed.
End HorizontalCompositionNaturalTransformation.