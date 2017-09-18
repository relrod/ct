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

Record Lattice {element : Type} :=
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

Record LOSet {A : Type} (o : PartiallyOrderedSet A) (l : @Lattice A) :=
  { meet_consistency : forall a b, le A o a b <-> a = meet l a b;
    join_consistency : forall a b, le A o a b <-> b = join l a b
  }.

Section Lattice.
  Context (A : Type).
  Context {l : @Lattice A}.
  Context {o : PartiallyOrderedSet A}.
  Context {ll : LOSet o l}.

  Theorem meet_glb :
    forall (a b : A),
    forall x,
      le A o x a /\ le A o x b <-> le A o x (meet l a b).
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
    rewrite (meet_comm l x (meet l a b)).
    rewrite <- (meet_assoc l a).
    rewrite <- (meet_assoc l a).
    rewrite (meet_comm l (meet l b x) a).
    rewrite (meet_assoc l a).
    rewrite (meet_assoc l a).
    rewrite (meet_assoc l a).
    rewrite meet_idem.
    reflexivity.
    assumption.
    apply (meet_consistency o l) in H.
    apply (meet_consistency o l).
    assumption.
    rewrite H.
    rewrite (meet_comm l x (meet l a b)).
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite (meet_comm l b (meet l x b)).
    rewrite <- meet_assoc.
    rewrite meet_idem.
    rewrite (meet_comm l x b).
    reflexivity.
    assumption.
  Qed.

  Theorem join_lub :
    forall (a b : A),
    forall x,
      le A o a x /\ le A o b x <-> le A o (join l a b) x.
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
    rewrite <- (join_assoc l a).
    rewrite (join_assoc l a).
    rewrite (join_assoc l a).
    rewrite (join_assoc l a).
    rewrite join_idem.
    reflexivity.
    assumption.
    apply (join_consistency o l) in H.
    apply (join_consistency o l).
    assumption.
    rewrite H.
    rewrite <- (join_assoc l a).
    rewrite (join_assoc l a).
    rewrite (join_comm l (join l a b) x).
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

(** * Lattice homomorphisms

A lattice homomorphism $f : A -> B$ where $A$ and $B$ are lattices, is a
function from the carrier set of $A$ to the carrier set of $B$ that preserves
meet, join, and where required, top and bottom.

We have:
  - \((x\) meet \(y) = f(x)\) meet \(f(y)\)
  - \(f(\top) = \top\)
  - \(f(\bot) = \bot\)
  - \((x\) join \(y) = f(x)\) join \(f(y)\)

A homomorphism with these laws is necessarily monotone, though we don't prove
that here right now.
*)

Record LatticeHomomorphism {t1 t2 : Type} (l1 : @Lattice t1) (l2 : @Lattice t2) :=
  { f :  t1 -> t2;
    lat_hom_pres_meet : forall a b, f (meet l1 a b) = meet l2 (f a) (f b);
    lat_hom_pres_join : forall a b, f (join l1 a b) = join l2 (f a) (f b)
  }.