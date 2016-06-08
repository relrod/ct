Require Import CT.Category.
Require Import CT.Instance.Category.
Require Import CT.Instance.Coq.Category.
Require Export Program.

(** F : A -> B *)
Record Functor (A B : Category) :=
  {  F_ob : A -> B;
     F_mor : forall {a b}, mor a b -> mor (F_ob a) (F_ob b);
     F_id_law : forall a, F_mor (id a) = id (F_ob a);
     F_comp_law : forall {a b c : ob} (f : mor a b) (g : mor b c),
         F_mor (comp f g) = comp (F_mor f) (F_mor g)
  }.

(** [F : A -> A]. An _endofunctor_ maps a category to itself. *)
Definition Endofunctor (C : Category) := Functor C C.

(** [F : AxB -> C]. _Bifunctors_ are functors from a product category to another
    category. *)
Program Definition Bifunctor (A B C : Category) := Functor (ProductCategory A B) C.

(** [F : C^op -> D]. A _contravariant functor_ flips morphisms. *)
Program Definition ContravariantFunctor (C D : Category) := Functor (C^op) D.

(** [F : (D^op)xC-> Set]. _Profunctors_ *)
(** Note: This definition might be wrong - I'm using [CoqType] for Set here.
    This feels many kinds of wrong. *)
Program Definition Profunctor (C D : Category) := Bifunctor (D^op) C CoqType.

Arguments F_ob {_ _} _ _.
Arguments F_mor {_ _} _ {_ _} _, {_ _} _ _ _ _.
Arguments F_id_law {_ _} _ _.
Arguments F_comp_law {_ _} _ {_ _ _} _ _.

(** Equivalence of functors *)
Theorem F_eq : forall A B (f1 f2 : Functor A B),
    @F_ob _ _ f1 = @F_ob _ _ f2 ->
    @F_mor _ _ f1 ~= @F_mor _ _ f2 ->
    f1 = f2.
Proof.
  intros.
  destruct f1, f2.
  simpl in H.
  simpl in H0.
  subst.
  subst.
  f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.