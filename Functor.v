Require Import Category.

(* F : A -> B *)
Class Functor (A B : Category) :=
  {  F_ob : A -> B;
     F_mor : forall {a b}, mor a b -> mor (F_ob a) (F_ob b);
     F_id_law : forall a, F_mor (id a) = id (F_ob a);
     F_comp_law : forall {a b c : ob} (f : mor a b) (g : mor b c),
         F_mor (comp f g) = comp (F_mor f) (F_mor g)
  }.