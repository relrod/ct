Require Import CT.Category.

(** * Generalized morhpisms

This abstracts over the notion of a morphism.
*)
Record Morphism {C : Category} :=
  { M_dom : ob C;
    M_cod : ob C;
    M_mor : mor M_dom M_cod
  }.