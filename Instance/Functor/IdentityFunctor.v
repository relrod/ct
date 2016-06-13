Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.Endofunctor.

Program Definition IdentityFunctor {C : Category} : @Endofunctor C :=
  {| F_ob := fun x => x;
     F_mor := fun _ _ f => f;
  |}.