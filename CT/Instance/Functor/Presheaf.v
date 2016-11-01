Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Coq.Category.
Require Import CT.Instance.Functor.ContravariantFunctor.

(** * Presheaves

A presheaf is a contravariant functor whose codomain is [Set].
In this case we use the category [CoqType] of Coq types instead of [Set].
*)
Program Definition Presheaf (C : Category) := ContravariantFunctor C CoqType.
