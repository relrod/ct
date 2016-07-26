Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Category.Opposite.

(** [F : C^op -> D]. A _contravariant functor_ flips morphisms. *)
Program Definition ContravariantFunctor (C D : Category) := Functor (C^op) D.