Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Isomorphism.
Require Import CT.Instance.Category.FunctorCategory.
Require Import CT.Instance.Functor.ComposeFunctor.
Require Import CT.Instance.Functor.IdentityFunctor.
Require Import CT.Instance.Isomorphism.
Require Import CT.Instance.NaturalTransformation.NaturalIsomorphism.
Require Import CT.Instance.NaturalTransformation.IdentityNaturalTransformation.

Record CategoryEquivalence (C D : Category) :=
  { F : Functor C D;
    G : Functor D C;
    ceq_nat_iso1 : NaturalIsomorphism (ComposeFunctor G F) (@IdentityFunctor D);
    ceq_nat_iso2 : NaturalIsomorphism (ComposeFunctor F G) (@IdentityFunctor C)
  }.

(** Equivalence of categories forms an equivalence relation. *)
Section CategoryEquivalence.
  Context {A B C : Category}.
  Section CategoryEquivalenceReflexivity.
    Program Definition category_equiv_refl_nat_iso :
      NaturalIsomorphism (ComposeFunctor (@IdentityFunctor C)
                                         (@IdentityFunctor C))
                         (@IdentityFunctor C).
    Proof.
      rewrite comp_identity_identity.
      apply IdentityIso.
      trivial.
      trivial.
    Qed.

    Program Definition CategoryEquivalenceReflexivity : CategoryEquivalence C C :=
      {| F := @IdentityFunctor C;
         G := @IdentityFunctor C;
         ceq_nat_iso1 := category_equiv_refl_nat_iso;
         ceq_nat_iso2 := category_equiv_refl_nat_iso
      |}.
  End CategoryEquivalenceReflexivity.

  Section CategoryEquivalenceSymmetry.
    Theorem CategoryEquivalenceSymmetry :
      CategoryEquivalence A B ->
      CategoryEquivalence B A.
    Proof.
      intros.
      destruct X.
      exists G0 F0.
      trivial.
      trivial.
    Qed.
  End CategoryEquivalenceSymmetry.

  Section CategoryEquivalenceTransitivity.
    Theorem CategoryEquivalenceTransitivity :
      CategoryEquivalence A B ->
      CategoryEquivalence B C ->
      CategoryEquivalence A C.
    Proof.
      intros.
      destruct X, X0.
      exists (ComposeFunctor F0 F1) (ComposeFunctor G1 G0).
      replace (ComposeFunctor (ComposeFunctor G1 G0) (ComposeFunctor F0 F1)) with
              (ComposeFunctor (ComposeFunctor G1 (ComposeFunctor G0 F0)) F1).
      Focus 2.
      rewrite functor_comp_assoc.
      rewrite functor_comp_assoc.
      trivial.
      admit. (* UGH! *)
    Admitted.
  End CategoryEquivalenceTransitivity.
End CategoryEquivalence.