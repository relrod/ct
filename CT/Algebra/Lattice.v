Require Import Order.PartiallyOrderedSet.
(** * Lattices

We take an algebraic rather than a topological view of lattices here.
In the future, we might encode a topological approach and prove them equivalent.

A lattice is a structure with meet, join, top, bottom, such that:
  - meet and join are idempotent, commutative, associative
  - join a (meet a b) = a, and, meet a (join a b) = a

(See https://ncatlab.org/nlab/show/lattice)
*)

(* TODO: We should formalize and abstract meet and join *)

Record Lattice (element : Type) :=
  { meet : element -> element -> element;
    join : element -> element -> element;

    meet_idem : forall a, meet a a = a;
    meet_comm : forall a b, meet a b = meet b a;
    meet_assoc : forall a b c, meet a (meet b c) = meet (meet a b) c;

    join_idem : forall a, join a a = a;
    join_comm : forall a b, join a b = join b a;
    join_assoc : forall a b c, join a (join b c) = join (join a b) c;

    absorption_1 : forall a b, join a (meet a b) = a;
    absorption_2 : forall a b, meet a (join a b) = a
  }.

Record LOSet {A : Type} (o : PartiallyOrderedSet A) (l : Lattice A) :=
  { meet_consistency : forall a b, le A o a b <-> a = meet A l a b;
    join_consistency : forall a b, le A o a b <-> b = join A l a b
  }.

Section Lattice.
  Context (A : Type).
  Context {l : Lattice A}.
  Context {o : PartiallyOrderedSet A}.
  Context {ll : LOSet o l}.

  Theorem meet_glb :
    forall (a b : A),
    forall x,
      le A o x a /\ le A o x b <-> le A o x (meet A l a b).
  Proof.
    split. intros.
    intuition.
    apply (meet_consistency o l) in H0.
    apply (meet_consistency o l) in H1.
    apply (meet_consistency o l).
    assumption.
    rewrite meet_assoc.
    rewrite <- H0.
    assumption. assumption. assumption.
    intros. split.
    apply (meet_consistency o l) in H.
    apply (meet_consistency o l).
    assumption.
    rewrite H.
    rewrite (meet_comm A l x (meet A l a b)).
    rewrite <- (meet_assoc A l a).
    rewrite <- (meet_assoc A l a).
    rewrite (meet_comm A l (meet A l b x) a).
    rewrite (meet_assoc A l a).
    rewrite (meet_assoc A l a).
    rewrite (meet_assoc A l a).
    rewrite meet_idem.
    reflexivity.
    assumption.
    apply (meet_consistency o l) in H.
    apply (meet_consistency o l).
    assumption.
    rewrite H.
    rewrite (meet_comm A l x (meet A l a b)).
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite (meet_comm A l b (meet A l x b)).
    rewrite <- meet_assoc.
    rewrite meet_idem.
    rewrite (meet_comm A l x b).
    reflexivity.
    assumption.
  Qed.

  Theorem join_lub :
    forall (a b : A),
    forall x,
      le A o a x /\ le A o b x <-> le A o (join A l a b) x.
  Proof.
    split. intros.
    intuition.
    apply (join_consistency o l) in H0.
    apply (join_consistency o l) in H1.
    apply (join_consistency o l).
    assumption.
    rewrite <- join_assoc.
    rewrite <- H1.
    apply H0.
    assumption.
    assumption.
    intros. split.
    apply (join_consistency o l) in H.
    apply (join_consistency o l).
    assumption.
    rewrite H.
    rewrite <- (join_assoc A l a).
    rewrite (join_assoc A l a).
    rewrite (join_assoc A l a).
    rewrite (join_assoc A l a).
    rewrite join_idem.
    reflexivity.
    assumption.
    apply (join_consistency o l) in H.
    apply (join_consistency o l).
    assumption.
    rewrite H.
    rewrite <- (join_assoc A l a).
    rewrite (join_assoc A l a).
    rewrite (join_comm A l (join A l a b) x).
    rewrite join_assoc.
    rewrite join_comm.
    rewrite join_assoc.
    rewrite join_assoc.
    rewrite join_assoc.
    rewrite join_idem.
    reflexivity.
    assumption.
  Qed.
End Lattice.