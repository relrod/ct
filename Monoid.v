Record Monoid {T : Type} :=
  { mu : T -> T -> T;
    one : T;
    monoid_assoc : forall x y z, mu x (mu y z) = mu (mu x y) z;
    monoid_left_one : forall x, mu one x = x;
    monoid_right_one : forall x, mu x one = x
  }.