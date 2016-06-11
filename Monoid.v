Require Import CT.Magma.
Require Import CT.Semigroup.

Set Primitive Projections.

Record Monoid {T : Type} :=
  { semigroup : @Semigroup T;
    one : T;
    monoid_left_one : forall x, semigroup.(magma).(mu) one x = x;
    monoid_right_one : forall x, semigroup.(magma).(mu) x one = x
  }.