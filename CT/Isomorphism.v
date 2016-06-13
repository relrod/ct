Require Import CT.Category.

(** Isomorphism between objects in a category C.

The idea is that if a morphism 'f' is an isomorphism, then there exists
an inverse function such that composing it on either side yields the
identity morphism. *)
Record Isomorphism {C : Category} (a b : @ob C) :=
  { to : mor a b;
    from : mor b a;
    inv_left : comp from to = id;
    inv_right : comp to from = id;
  }.