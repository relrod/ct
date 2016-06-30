Require Import CT.Category.

(** * Section

Given objects \(a, b\) in a category \(C\), a "section" of a \(C\)-morphism
\(f : a \to b\) is a right-inverse \(g : b \to a\) such that
\(f \circ g = id_b\).
 *)
Record Section {C : Category} {a b : ob C} (f : mor a b) :=
  { section : mor b a;
    section_law : comp section f = id b
  }.