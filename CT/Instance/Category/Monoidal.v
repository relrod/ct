Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Category.ProductCategory.
Require Import CT.Instance.Functor.Endofunctor.
Require Import CT.Instance.Functor.ProductFunctor.
Require Import CT.Instance.NaturalTransformation.NaturalIsomorphism.

(** A monoidal category is the vertical categorification of the set theory
    concept of a [Monoid] (such as that defined in [CT.Algebra.Monoid]).

    A monoidal category is a category \(C\) together with a functor
    \(C \times C \to C\) which performs the tensor product, an identity element
    \(I\) which lives in \(C\), and three natural isomorphisms which serve to
    force associativity of the tensor operator, and that \I(\) acts as a left
    and right identity. The coherence conditions about the natural isomorphisms
    give rise to laws known as the triangle identity and the pentagon identity.
 *)
Record MonoidalCategory (C : Category) :=
  { tensor : Tensor C;
    I : @ob C;

    (* Coherence natural isomorphisms go here: *)
  }.