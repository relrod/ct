Require Import CT.Category.

Set Universe Polymorphism.

(** Isomorphism between objects in a category.

The idea is that if a morphism \(f\) is an isomorphism, then there exists
an inverse function such that composing it on either side yields the
identity morphism.

That is: Let \(C\) be a category and \(a, b\) be objects in C. Then a morphism
\(f : a \to b\) is an isomorphism if there exists another morphism
\(g : b \to a\) such that \(g \circ f = id_a\) and \(f \circ g = id_b\).

In this case, \(a\) and \(b\) are said to be isomorphic to each other.
 *)
Record Isomorphism {C : Category} (a b : @ob C) :=
  { to : mor a b;
    from : mor b a;
    inv_left : comp from to = id;
    inv_right : comp to from = id
  }.