Require Import CT.Category.
Require Import CT.Morphism.
Require Import ProofIrrelevance.

Set Implicit Arguments.

Section ArrowCategory.
  Variable (C : Category).

  (** * Morphisms in the arrow category.

  These correspond to a commutative square as per
  https://ncatlab.org/nlab/show/arrow+category#definition
  *)
  Definition morphism a b :=
    { m : (mor (M_dom a) (M_dom b) * mor (M_cod a) (M_cod b)) |
      comp (M_mor a) (snd m) = comp (fst m) (@M_mor C b) }.

  (* This is annoying. *)
  Lemma exist_injective :
    forall A (f : A -> Prop) a b a' b',
      a = b -> exist f a a' = exist f b b'.
  Proof.
    intros.
    subst.
    f_equal.
    apply proof_irrelevance.
  Qed.

  (** * Arrow categories *)
  Program Definition ArrowCategory : Category :=
    {| ob := @Morphism C;
       mor := morphism
    |}.
  Next Obligation.
  Proof.
    destruct a, b, c, X, X0.
    unfold morphism.
    simpl in *.
    destruct x, x0.
    simpl in *.
    exists (comp m m1, comp m0 m2).
    simpl.
    rewrite <- assoc.
    rewrite <- e0.
    repeat rewrite assoc.
    rewrite <- e.
    reflexivity.
  Defined.
  Next Obligation.
  Proof.
    destruct a.
    unfold morphism.
    exists (id (M_dom), id (M_cod)).
    rewrite id_right.
    rewrite id_left.
    reflexivity.
  Defined.
  Next Obligation.
  Proof.
    destruct a, b, c, d.
    destruct f, g, h.
    destruct x, x0, x1.
    simpl in *.
    apply exist_injective.
    repeat rewrite assoc.
    reflexivity.
  Defined.
  Next Obligation.
  Proof.
    rewrite ArrowCategory_obligation_3.
    reflexivity.
  Defined.
  Next Obligation.
  Proof.
    destruct a, b, f.
    simpl in *.
    destruct x.
    apply exist_injective.
    assert (comp id m = m).
    rewrite id_left.
    reflexivity.
    rewrite H.
    assert (comp id m0 = m0).
    rewrite id_left.
    reflexivity.
    rewrite H0.
    reflexivity.
  Qed.
  Next Obligation.
  Proof.
    destruct a, b, f.
    simpl in *.
    destruct x.
    apply exist_injective.
    assert (comp m id = m).
    rewrite id_right.
    reflexivity.
    rewrite H.
    assert (comp m0 id = m0).
    rewrite id_right.
    reflexivity.
    rewrite H0.
    reflexivity.
  Qed.

  (* Isn't LTac pretty? :P *)
End ArrowCategory.