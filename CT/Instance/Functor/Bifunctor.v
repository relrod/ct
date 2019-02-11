Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Category.ProductCategory.
Require Import CT.Instance.Functor.Endofunctor.

(** [F : AxB -> C]. _Bifunctors_ are functors from a product category to another
    category. These (or rather their specialized form [ProductFunctor]) show up
    as tensors in [MonoidalCategory] instances.
*)
Program Definition Bifunctor (A B C : Category) := Functor (ProductCategory A B) C.

(* TODO: Explain this better. *)
(** Given two morphisms \(f, g\), do the "right thing" by applying them to
    the first and second components on both ends of a morphism respectively,
    thus lifting it into the codomain category of the given (implicit)
    functor. *)
Definition bimap
           {A B C : Category}
           {F : Bifunctor A B C}
           {a b : ob A}
           {c d : ob B}
           (f : mor a b)
           (g : mor c d) :
  mor (F_ob F (a, c)) (F_ob F (b, d)) :=
  @F_mor (ProductCategory A B) C F (a, c) (b, d) (f, g).

(* TODO: Write a bunch of theorems about bimap. *)