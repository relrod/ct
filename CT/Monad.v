Require Import CT.Category.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.Functor.ComposeFunctor.
Require Import CT.Instance.Functor.Endofunctor.
Require Import CT.Instance.Functor.IdentityFunctor.
Require Export CT.Instance.NaturalTransformation.HCNaturalTransformation.
Require Export CT.Instance.NaturalTransformation.IdentityNaturalTransformation.
Require Export CT.Instance.NaturalTransformation.VCNaturalTransformation.
Require Import ProofIrrelevance.


(** Monad.

A monad is an endofunctor on \(C\) together with two natural transformations,
\(\eta\) and \(\mu\) which satisfy two coherence conditions.
 *)

Record Monad
       {C : Category}
       (T : Endofunctor C)
       (eta : NaturalTransformation (@IdentityFunctor C) T)
       (mu : NaturalTransformation (ComposeFunctor T T) T) :=

  { (* Coherence: *)
    monad_coherence_assoc :
      nt_components (VCNaturalTransformation (HCNaturalTransformation mu (IdentityNaturalTransformation T)) mu) =
      nt_components (VCNaturalTransformation (HCNaturalTransformation (IdentityNaturalTransformation T) mu) mu);

    monad_coherence_id_1 :
      nt_components (VCNaturalTransformation (HCNaturalTransformation eta (IdentityNaturalTransformation T)) mu) =
      nt_components (IdentityNaturalTransformation T);

    monad_coherence_id_2 :
      nt_components (VCNaturalTransformation (HCNaturalTransformation (IdentityNaturalTransformation T) eta) mu) =
      nt_components (IdentityNaturalTransformation T);
  }.

Theorem monad_equivalence :
  forall {C}
         {T : Endofunctor C}
         (eta : NaturalTransformation (@IdentityFunctor C) T)
         (mu : NaturalTransformation (ComposeFunctor T T) T)
         (mon1 mon2 : @Monad C T eta mu),
    mon1 = mon2.
Proof.
  intros.
  destruct mon1, mon2.
  f_equal;
    apply proof_irrelevance.
Qed.