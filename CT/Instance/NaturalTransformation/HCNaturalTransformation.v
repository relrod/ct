Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.Functor.ComposeFunctor.

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