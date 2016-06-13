Require Import CT.Category.
Require Import CT.Functor.

Program Definition OppositeFunctor {C D : Category} (F : Functor C D) : Functor (C^op) (D^op) :=
  {| F_ob := F_ob F;
     F_mor := fun _ _ h => F_mor F _ _ h;
     F_id_law := fun a => F_id_law F a;
     F_comp_law := fun _ _ _ f g => F_comp_law F g f
  |}.