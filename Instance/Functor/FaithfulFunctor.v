Require Import CT.Category.
Require Import CT.Functor.

(** * Faithful Functors

A "faithful" functor is one that is injective on hom-sets. That is,
A functor \(F : C \to D\) is _faithful_ if \(\forall x, y \in C\), the function
\(F : C(x, y) \to D(F(x), F(y))\) is injective.

So we require a [Functor] and a proof that injectivity of hom-sets is satisfied.
*)
Section FaithfulFunctor.
  Context {A B : Category}.
  Variable (F : Functor A B).

  (* Injectivity of [F_mor] *)
  Definition FaithfulFunctor :=
    forall {a b} (f : mor A a b) (g : mor A a b),
      F_mor F f = F_mor F g -> f = g.
End FaithfulFunctor.