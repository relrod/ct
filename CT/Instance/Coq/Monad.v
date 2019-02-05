Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Monad.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.Coq.Category.
Require Import CT.Instance.Coq.Functor.
Require Import CT.Instance.Functor.Endofunctor.
Require Import CT.Instance.Functor.ComposeFunctor.
Require Import CT.Instance.Functor.IdentityFunctor.
Require Import FunctionalExtensionality List.

Section CoqOptionMonad.
  Program Definition CoqOptionMuNT :
    NaturalTransformation
      (ComposeFunctor CoqOptionFunctor CoqOptionFunctor)
      CoqOptionFunctor :=
    {| nt_components := fun x y => match y with
                                   | None => None
                                   | Some a => a
                                   end
    |}.
  Proof.
    Next Obligation.
      extensionality q.
      destruct q.
      simpl.
      reflexivity.
      simpl.
      reflexivity.
    Qed.
    Next Obligation.
      extensionality q.
      destruct q.
      simpl.
      reflexivity.
      simpl.
      reflexivity.
    Qed.

  Program Definition CoqOptionEtaNT :
    NaturalTransformation IdentityFunctor CoqOptionFunctor :=
    {| nt_components := @Some
    |}.

  Program Definition CoqOptionMonad : @Monad CoqType :=
    {| T := CoqOptionFunctor;
       eta := CoqOptionEtaNT;
       mu := CoqOptionMuNT
    |}.
  Proof.
    Next Obligation.
      extensionality q.
      extensionality x.
      destruct x.
      simpl.
      destruct o.
      simpl.
      reflexivity.
      reflexivity.
      reflexivity.
    Qed.
    Next Obligation.
      extensionality q.
      extensionality x.
      destruct x.
      simpl.
      reflexivity.
      simpl.
      reflexivity.
    Qed.
End CoqOptionMonad.