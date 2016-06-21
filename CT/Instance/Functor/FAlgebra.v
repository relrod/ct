Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.Endofunctor.

(** * F-Algebras

(a.k.a. "an algebra over an endofunctor").

Given a category \(C\) and endofunctor \(F\) on \(C\), an F-algebra over \(F\)
is given by an object \(X \in\) ob \(C\) along with a morphism
\(\alpha : F(X) \to X\).

Here \(X\) is called the _carrier_ of the algebra.

See
#<a href="https://ncatlab.org/nlab/show/algebra+for+an+endofunctor">nlab</a>#
for more details.
 *)
Section FAlgebra.
  Context {C : Category}.
  Context {F : Endofunctor C}.

  Record FAlgebra :=
    { FA_ob : ob C;
      FA_alpha : mor C (F_ob F FA_ob) FA_ob
    }.
End FAlgebra.