Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.

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
  Variable (N : NaturalTransformation F G) (M : NaturalTransformation G H).

  Program Definition CompositionNaturalTransformation : NaturalTransformation F H :=
    {| nt_components := fun g => comp (nt_components F G N g) (nt_components G H M g) |}.
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