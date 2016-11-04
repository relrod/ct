Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.Bifunctor.
Require Import CT.Instance.Category.Opposite.
Require Import CT.Instance.Coq.Category.

(** * Hom Functors

A hom functor for a category \(C\) is a functor \(C^{op} \times C\) \to Set\).

In our case, we use [CoqType] in place of Set.

The functor must send \((c, c') \in ob(C^{op} \times C) to the set of morphisms
\(c \to c'\) in \(C\), and send a pair of morphisms
\((f^{op} : c \to d, g : c' \to d')\) to the function
\(Hom_C(c, c') \to Hom_C(d, d')\) which sends
\((q : c \to c') \to g \circ q \circ f\).

*)
Section HomFunctor.
  Context {C : Category}.
  Variable (F : Bifunctor C (C^op) CoqType).

  (* TODO!! *)

End HomFunctor.