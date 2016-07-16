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

(** The composition of two [Isomorphism]s is again an [Isomorphism]. *)
Theorem iso_comp_iso
        {C : Category}
        {a b c : C}
        (x : @Isomorphism C a b)
        (y : @Isomorphism C b c) :
  @Isomorphism C a c.
Proof.
  destruct x, y.
  exists (comp to0 to1) (comp from1 from0).
  rewrite assoc.
  rewrite <- (assoc C from1).
  rewrite inv_left0.
  rewrite id_right.
  assumption.
  rewrite assoc.
  rewrite <- (assoc C to0).
  rewrite inv_right1.
  rewrite id_right.
  assumption.
Defined.