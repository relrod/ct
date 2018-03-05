Require Import CT.Algebra.Lattice.
Require Import CT.Order.PartiallyOrderedSet.
Require Import Coq.Program.Basics.
Require Setoid.

(** * Boolean Algebras

There are many equivalent definitions of a boolean algebra, but the one we take
builds on our definition of a [Lattice]. In this definition, a [BooleanAlgebra]
is a [Lattice] with an additional function [notB] which is an endomorphism over
the carrier set that satisfies:

  - le (meet a b) c  iff  le a (join (notB b) c)

We use [notB] instead of [not] so as not to conflict with
[not : Prop -> Prop].
*)

Record BooleanAlgebra :=
  { L :> Lattice;
    notB : element L -> element L;
    condB : forall a b c : element L,
        le (poset L) (meet L a b) c <-> le (poset L) a (join L (notB b) c)
  }.

(* Play around in the context of [Prop]. *)
(*
Section ToyProp.
  Program Definition prop_poset : PartiallyOrderedSet :=
    {| le := fun a b => (a = (b /\ a)) <-> ((a \/ b) = b) |}.
  Next Obligation.

  Program Definition prop_lat : Lattice :=
    {| element := Prop;
       poset := prop_poset;
       meet := fun a b => a /\ b;
       join := fun a b => a \/ b;
    |}.
  Next Obligation.
*)