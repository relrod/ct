Require Import CT.Category.
Require Import CT.Functor.

(** [F : A -> A]. An _endofunctor_ maps a category to itself. *)
Program Definition Endofunctor (C : Category) := Functor C C.
