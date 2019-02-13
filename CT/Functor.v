Require Import CT.Category.
Require Import CT.Isomorphism.
Require Export Program.

(** * F : A -> B

Functors map objects in one category to objects in another category and also
morhpisms in the first category to morphisms in the second category.

They must obey the identity and composition laws encoded below.
 *)
Record Functor (A B : Category) :=
  {  F_ob : A -> B;
     F_mor : forall {a b}, mor a b -> mor (F_ob a) (F_ob b);
     F_id_law : forall a, F_mor (id a) = id (F_ob a);
     F_comp_law : forall {a b c : ob} (f : mor a b) (g : mor b c),
         F_mor (comp f g) = comp (F_mor f) (F_mor g)
  }.

Arguments F_ob {_ _} _ _.
Arguments F_mor {_ _} _ {_ _} _, {_ _} _ _ _ _.
Arguments F_id_law {_ _} _ _.
Arguments F_comp_law {_ _} _ {_ _ _} _ _.

(** Equivalence of functors, by proof irrelevance *)
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

(** [Functor]s preserve isomorphism. *)
Theorem functor_pres_iso :
  forall {C D : Category}
         (F : Functor C D)
         (a b : ob C)
         (f : @Isomorphism C a b),
    @Isomorphism D (F_ob F a) (F_ob F b).
Proof.
  intros.
  destruct f.
  exists (F_mor F to) (F_mor F from).
  - rewrite <- F_comp_law.
    rewrite inv_left.
    rewrite F_id_law.
    trivial.
  - rewrite <- F_comp_law.
    rewrite inv_right.
    rewrite F_id_law.
    trivial.
Qed.