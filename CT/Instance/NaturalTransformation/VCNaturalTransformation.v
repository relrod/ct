Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.NaturalTransformation.IdentityNaturalTransformation.

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

(** Vertical composition of natural transformations associates. *)
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

(** The identity natural transformations acts as left vertical compositional
    identity *)
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

(** The identity natural transformations acts as right vertical compositional
    identity *)
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