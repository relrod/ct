Require Import Coq.Program.Tactics.
Require Import CT.Category.
Require Import CT.Functor.

Program Definition OppositeFunctor {C D : Category} (F : Functor C D) : Functor (C^op) (D^op) :=
  {| F_ob := F_ob F;
     F_mor := fun _ _ h => F_mor F _ _ h;
     F_id_law := fun a => F_id_law F a;
     F_comp_law := fun _ _ _ f g => F_comp_law F g f
  |}.

Program Definition IdentityFunctor {C : Category} (F : Functor C C) : Functor C C :=
  {| F_ob := F_ob F;
     F_mor := fun _ _ h => F_mor F _ _ h;
     F_id_law := fun a => F_id_law F a;
     F_comp_law := fun _ _ _ f g => F_comp_law F f g
  |}.

Program Definition ComposeFunctor {A B C : Category} (F : Functor A B) (G : Functor B C): Functor A C :=
  {| F_ob := fun c => F_ob G (F_ob F c);
     F_mor := fun _ _ f => F_mor G (F_mor F f);
  |}.
Next Obligation.
Proof.
  intros.
  rewrite F_id_law.
  rewrite F_id_law.
  reflexivity.
Qed.
Next Obligation.
Proof.
  rewrite F_comp_law.
  rewrite F_comp_law.
  reflexivity.
Qed.