Require Import CT.Category.
Require Export Program.

(** F : A -> B *)
Record Functor (A B : Category) :=
  {  F_ob : A -> B;
     F_mor : forall {a b}, mor a b -> mor (F_ob a) (F_ob b);
     F_id_law : forall a, F_mor (id a) = id (F_ob a);
     F_comp_law : forall {a b c : ob} (f : mor a b) (g : mor b c),
         F_mor (comp f g) = comp (F_mor f) (F_mor g)
  }.

(** F : A -> A. An endofunctor maps a category to itself. *)
Definition Endofunctor {C : Category} := Functor C C.

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