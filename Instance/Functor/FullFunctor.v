Require Import CT.Category.
Require Import CT.Functor.

(** * Full Functors

A "full" functor is one that is surjective on hom-sets. That is,
A functor \(F : C \to D\) is _full_ if \(\forall x, y \in C\), the function
\(F : C(x, y) \to D(F(x), F(y))\) is surjective.

So we require a [Functor] and a proof that surjectivity of hom-sets is
satisfied.
*)
Section FullFunctor.
  Context {A B : Category}.
  Variable (F : Functor A B).

  (* Surjectivity of [F_mor] *)
  Definition FullFunctor :=
    forall {a b} (f : mor B (F_ob F a) (F_ob F b)),
      { f' : mor A a b | F_mor F f' = f }.
End FullFunctor.