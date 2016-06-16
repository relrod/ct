Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.Bifunctor.

(** A product functor \(F\) on a category \(C\) is a [Bifunctor]:
\(F : C \times C \to C\). *)
Program Definition ProductFunctor (C : Category) := Bifunctor C C C.