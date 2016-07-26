Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.Bifunctor.
Require Import CT.Instance.Coq.Category.
Require Import CT.Instance.Category.Opposite.

(** [F : (D^op)xC-> Set]. _Profunctors_ *)
(** Note: This definition might be wrong - I'm using [CoqType] for Set here.
    This feels many kinds of wrong. *)
Program Definition Profunctor (C D : Category) := Bifunctor (D^op) C CoqType.