Require Import Coq.Program.Tactics.
Require Import CT.Category.
Require Import CT.Functor.

Program Definition ComposeFunctor {A B C : Category} (F : Functor A B) (G : Functor B C): Functor A C :=
  {| F_ob := fun c => F_ob G (F_ob F c);
     F_mor := fun _ _ f => F_mor G (F_mor F f);
  |}.
Next Obligation.
Proof.
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