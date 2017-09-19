Require Import CT.Order.PartiallyOrderedSet.
Require Import Coq.Program.Tactics.
Require Import ProofIrrelevance.

(** * Lattices

We take an algebraic rather than a topological view of lattices here.
In the future, we might encode a topological approach and prove them equivalent.

A lattice is a structure with meet, join, top, bottom, such that:
  - meet and join are idempotent, commutative, associative
  - join a (meet a b) = a, and, meet a (join a b) = a

(See https://ncatlab.org/nlab/show/lattice)
*)

(* TODO: We should formalize and abstract meet and join *)

Record Lattice :=
  { element : Type;
    poset : @PartiallyOrderedSet element;
    meet : element -> element -> element;
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

Record LOSet :=
  { lattice : Lattice;
    meet_consistency : forall a b, le (poset lattice) a b <-> a = meet lattice a b;
    join_consistency : forall a b, le (poset lattice) a b <-> b = join lattice a b
  }.

Section Lattice.
  Context {loset : LOSet}.
  Definition lat := lattice loset.
  Definition A := element lat.
  Definition o := poset lat.

  Theorem meet_glb :
    forall a b x,
      le o x a /\ le o x b <-> le o x (meet lat a b).
  Proof.
    split. intros.
    intuition.
    apply (meet_consistency loset) in H0.
    apply (meet_consistency loset) in H1.
    apply (meet_consistency loset).
    rewrite H0.
    rewrite meet_assoc.
    rewrite (meet_comm (lattice loset) x a).
    rewrite (meet_comm lat (meet (lattice loset) a x)).
    rewrite meet_assoc.
    rewrite meet_idem.
    rewrite H1.
    rewrite (meet_assoc (lattice loset) a).
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite meet_idem.
    reflexivity.
    intros. split.
    apply (meet_consistency loset) in H.
    apply (meet_consistency loset).
    rewrite H.
    rewrite meet_comm.
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite (meet_comm lat b (meet lat x a)).
    rewrite <- meet_assoc.
    rewrite (meet_comm lat a (meet lat x (meet lat a b))).
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite (meet_comm lat a (meet lat b a)).
    rewrite <- meet_assoc.
    rewrite meet_idem.
    rewrite (meet_comm lat b a).
    rewrite meet_assoc.
    rewrite meet_comm.
    reflexivity.
    apply (meet_consistency loset) in H.
    apply (meet_consistency loset).
    rewrite H.
    rewrite meet_comm.
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite <- meet_assoc.
    rewrite (meet_comm lat b (meet lat x b)).
    rewrite <- meet_assoc.
    rewrite meet_idem.
    rewrite (meet_comm lat x b).
    reflexivity.
Qed.


  Theorem join_lub :
    forall a b x,
      le o a x /\ le o b x <-> le o (join lat a b) x.
  Proof.
    (* TODO: Redo this proof. *)
    Admitted.
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

Record LatticeHomomorphism (l1 l2 : Lattice) :=
  { f :  element l1 -> element l2;
    lat_hom_pres_meet : forall a b, f (meet l1 a b) = meet l2 (f a) (f b);
    lat_hom_pres_join : forall a b, f (join l1 a b) = join l2 (f a) (f b)
  }.

(** * Composition of lattice homomorphisms. *)
Program Definition lattice_hom_composition
        {A : Lattice}
        {B : Lattice}
        {C : Lattice}
        {T : element A}
        {U : element B}
        {V : element C}
        (map1 : LatticeHomomorphism A B)
        (map2 : LatticeHomomorphism B C) :
  LatticeHomomorphism A C :=
  {| f := fun a => (f B C map2) ((f A B map1) a) |}.
Next Obligation.
Proof.
  destruct A0, B, C, map1, map2.
  simpl in *.
  rewrite lat_hom_pres_meet0.
  rewrite lat_hom_pres_meet1.
  reflexivity.
Qed.
Next Obligation.
  destruct A0, B, C, map1, map2.
  simpl in *.
  rewrite lat_hom_pres_join0.
  rewrite lat_hom_pres_join1.
  reflexivity.
Qed.

(** * Equality of lattice homomorphisms, assuming proof irrelevance. *)
Theorem lattice_hom_eq : forall F G (N M : LatticeHomomorphism F G),
    @f F G M = @f F G N ->
    N = M.
Proof.
  intros.
  destruct N, M.
  simpl in *.
  subst.
  f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

(** * Identity lattice homomorphism. *)
Program Definition lattice_hom_id
        {A : Lattice}
        {T : element A}:
  LatticeHomomorphism A A :=
  {| f := fun a => a |}.

(** * Association of composition of lattice homomorphisms. *)
Program Definition lattice_hom_composition_assoc
        {A B C D : Lattice}
        {T : element A}
        {U : element B}
        {V : element C}
        {W : element D}
        (f : LatticeHomomorphism A B)
        (g : LatticeHomomorphism B C)
        (h : LatticeHomomorphism C D) :
  lattice_hom_composition f (lattice_hom_composition g h) =
  lattice_hom_composition (lattice_hom_composition f g) h.
Proof.
  destruct f, g, h.
  apply lattice_hom_eq.
  simpl.
  reflexivity.
Qed.
