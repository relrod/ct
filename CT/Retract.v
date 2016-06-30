Require Import CT.Category.

(** * Retracts

A "retract" of an object \(b\) in a category \(C\) is an object \(a \in Ob(C)\)
such that there exists morphisms \(f : a \to b\) and \(r : b \to a\) where
\(r \circ f = id_a\). The morphism \(r\) is a "retraction" of \(b\) onto \(a\).
 *)
Record Retract {C : Category} {a b : ob C} (f : mor a b) :=
  { retraction : mor b a;
    retraction_law : comp f retraction = id a
  }.