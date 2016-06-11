Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.Functor.
Require Import FunctionalExtensionality.

Program Definition IdentityNaturalTransformation {A B : Category} (F : Functor A B) :
  NaturalTransformation F F :=
  {| nt_components := fun _ => id
  |}.
Next Obligation.
Proof.
  rewrite id_left.
  rewrite id_right.
  reflexivity.
Qed.
Next Obligation.
Proof.
  symmetry.
  apply IdentityNaturalTransformation_obligation_1.
Qed.

(** * Vertical Composition of Natural Transformations

From wikipedia:

If η : F → G and ε : G → H are natural transformations between functors
F,G,H : C → D, then we can compose them to get a natural transformation
εη : F → H. This is done componentwise: (εη)X = εXηX. This "vertical
composition" of natural transformation is associative and has an identity.
*)
Section VCNaturalTransformation.
  Context {C D : Category} {F G H : Functor C D}.
  Variable (eta : NaturalTransformation F G).
  Variable (epsilon : NaturalTransformation G H).
  Variable X : ob C.
  Check nt_components F G eta X.
  Check nt_components G H epsilon X.
  Program Definition VCNaturalTransformation : NaturalTransformation F H :=
    {| nt_components := fun X => comp (nt_components F G eta X) (nt_components G H epsilon X) |}.
  Next Obligation.
  Proof.
    rewrite assoc.
    rewrite nt_commutes.
    repeat rewrite assoc_sym.
    rewrite nt_commutes_sym.
    reflexivity.
  Qed.
  Next Obligation.
    symmetry.
    apply VCNaturalTransformation_obligation_1.
  Qed.
End VCNaturalTransformation.

(** Composition of natural transformations associates. *)
Theorem VCNaturalTransformation_assoc :
  forall C D F G H I
         (N : @NaturalTransformation C D H I)
         (O : @NaturalTransformation C D G H)
         (P : @NaturalTransformation C D F G),
           VCNaturalTransformation (VCNaturalTransformation P O) N =
           VCNaturalTransformation P (VCNaturalTransformation O N).
Proof.
  intros.
  apply nt_eq.
  simpl.
  extensionality g.
  rewrite assoc.
  reflexivity.
Qed.

(** The identity natural transformations acts as left compositional identity *)
Theorem VCNaturalTransformation_id_left :
  forall C D F G
         (N : @NaturalTransformation C D F G),
    VCNaturalTransformation (IdentityNaturalTransformation F) N = N.
Proof.
  intros.
  apply nt_eq.
  simpl.
  extensionality g.
  rewrite id_left.
  reflexivity.
Qed.

(** The identity natural transformations acts as right compositional identity *)
Theorem VCNaturalTransformation_id_right :
  forall C D F G
         (N : @NaturalTransformation C D F G),
    VCNaturalTransformation N (IdentityNaturalTransformation G) = N.
Proof.
  intros.
  apply nt_eq.
  simpl.
  extensionality g.
  rewrite id_right.
  reflexivity.
Qed.

(** * Horizontal Composition of Natural Transformations

From wikipedia:

Natural transformations also have a "horizontal composition". If η : F → G is a
natural transformation between functors F,G : C → D and ε : J → K is a natural
transformation between functors J,K : D → E, then the composition of functors
allows a composition of natural transformations εη : JF → KG. This operation is
also associative with identity, and the identity coincides with that for
vertical composition.
*)
Section HCNaturalTransformation.
  Context {C D E : Category} {F G : Functor C D} {J K : Functor D E}.
  Variable mu : NaturalTransformation F G.
  Variable epsilon : NaturalTransformation J K.
  Let JF := ComposeFunctor F J.
  Let KG := ComposeFunctor G K.

  Program Definition HCNaturalTransformation : NaturalTransformation JF KG :=
    {| nt_components :=
         fun X => comp (nt_components J K epsilon (F_ob F X)) (F_mor K (nt_components F G mu X))
    |}.
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
    apply HCNaturalTransformation_obligation_1.
  Qed.
End HCNaturalTransformation.