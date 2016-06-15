Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.NaturalTransformation.HCNaturalTransformation.
Require Import CT.Instance.NaturalTransformation.VCNaturalTransformation.
Require Import FunctionalExtensionality.

(** * Interchange of horizontal/vertical composition

Given functors \(F\), \(G\), \(H\) : \(C \to D\) and \(F'\), \(G'\), \(H'\) :
\(D \to E\), and natural transformations \(\alpha : F \Rightarrow G\),
\(\beta : G \Rightarrow H\), \(\alpha' : F' \Rightarrow G'\), and
\(\beta' : G' \Rightarrow H'\), then the following holds:

$$$$
(\beta' \circ \alpha') * (\beta \circ \alpha) = (\beta' * \beta) \circ (\alpha' * \alpha) : F' \circ F \to H' \circ H
$$$$
*)
Section NaturalTransformationInterchange.
  Context {A A' A'' : Category}.
  Context {F G H : Functor A A'}.
  Context {F' G' H' : Functor A' A''}.
  Context {alpha : NaturalTransformation F G}.
  Context {beta : NaturalTransformation G H}.
  Context {alpha' : NaturalTransformation F' G'}.
  Context {beta' : NaturalTransformation G' H'}.

  Let l := HCNaturalTransformation (VCNaturalTransformation alpha beta) (VCNaturalTransformation alpha' beta').
  Let r := VCNaturalTransformation (HCNaturalTransformation alpha alpha') (HCNaturalTransformation beta beta').

  Theorem NaturalTransformationInterchange : l = r.
  Proof.
    apply nt_eq.
    simpl.
    extensionality X.
    rewrite F_comp_law.
    repeat rewrite assoc.
    match goal with
      [|- (comp ?B ?A = comp ?C ?A)] =>
      let H := fresh in
      cut (B = C); [intro H; rewrite H; trivial|]
    end.
    repeat rewrite assoc_sym.
    match goal with
      [|- (comp ?B ?A = comp ?B ?C)] =>
      let H := fresh in
      cut (A = C); [intro H; rewrite H; trivial|]
    end.
    rewrite <- nt_commutes.
    reflexivity.
  Qed.
End NaturalTransformationInterchange.