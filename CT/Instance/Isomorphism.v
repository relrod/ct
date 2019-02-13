Require Import CT.Category.
Require Import CT.Isomorphism.

Set Universe Polymorphism.

(** The identity isomorphism between objects. Each object in C is isomorphic to
itself, by definition. *)
Program Definition IdentityIso {C : Category} (a : @ob C) : Isomorphism a a :=
  {| to := id;
     from := id
  |}.
Next Obligation.
Proof.
  rewrite id_left. reflexivity.
Qed.
Next Obligation.
Proof.
  rewrite id_right. reflexivity.
Qed.

(** * Isomorphism is preserved under inverse.

That is, if [Isomorphism a b], then [Isomorphism b a].
*)
Program Definition InverseIso
        {C : Category}
        {a b : @ob C}
        (iso : Isomorphism a b) : Isomorphism b a :=
  {| to := from a b iso;
     from := to a b iso
  |}.
Next Obligation.
Proof.
  destruct iso.
  simpl.
  assumption.
Qed.
Next Obligation.
  destruct iso.
  simpl.
  assumption.
Qed.

(** * Isomorphism is preserved under composition.

Let \(C\) be a category and \(a, b, c\) be objects in \(C\). Let
\(f : a \to b\), and \(g : b \to c\) be isomorphisms in \(C\). Then
\(g \circ f : a \to c\) is also an isomorphism.
*)
Theorem iso_comp_iso
        {C : Category}
        {a b c : @ob C}
        (f : Isomorphism a b)
        (g : Isomorphism b c) :
  Isomorphism a c.
Proof.
  destruct f, g.
  exists (comp to to0) (comp from0 from).
  rewrite assoc.
  rewrite <- (assoc C from0).
  rewrite inv_left.
  rewrite id_right.
  assumption.
  rewrite assoc.
  rewrite <- (assoc C to).
  rewrite inv_right0.
  rewrite id_right.
  assumption.
Defined.

(** The three above derivations ([IdentityIso], [InverseIso], [iso_comp_iso])
together form an equivalence relation. At some point we should use
[Coq.Relations.Relation_Definitions] to make it so.
*)