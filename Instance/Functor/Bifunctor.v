Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Category.ProductCategory.

(** [F : AxB -> C]. _Bifunctors_ are functors from a product category to another
    category. *)
Program Definition Bifunctor (A B C : Category) := Functor (ProductCategory A B) C.