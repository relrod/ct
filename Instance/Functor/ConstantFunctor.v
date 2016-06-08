Require Import Coq.Program.Tactics.
Require Import CT.Category.
Require Import CT.Functor.

Program Definition ConstantFunctor {C D : Category} (a : @ob D) : Functor C D :=
  {| F_ob := fun _ => a;
     F_mor := fun _ _ _ => id;
  |}.
Next Obligation.
Proof.
  rewrite id_left. reflexivity.
Qed.