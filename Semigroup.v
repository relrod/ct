Require Import CT.Magma.

Set Primitive Projections.

Record Semigroup {T : Type} :=
  { magma : @Magma T;
    semigroup_assoc : forall x y z, magma.(mu) x (magma.(mu) y z) = magma.(mu) (magma.(mu) x y) z;
  }.