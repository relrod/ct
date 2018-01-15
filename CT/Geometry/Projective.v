(** Synthetic Projective Geometry

Following the work outlined here:
  http://www.maths.ed.ac.uk/~aar/papers/beutel.pdf
*)

Require Import Coq.Relations.Relations.

(** Geometry

A geometry is a set together with a so-called "incidence" relation that is
symmetric and reflexive. That is, a set together with a tolerance relation
(https://en.wikipedia.org/wiki/Tolerance_relation)

Specifically in our case, it's a set (rather, a type), with a [Relation]
and proofs that the [Relation] is a tolerance relation.
*)

Record Geometry (t : Type) :=
  { geom_incidence : relation t;
    geom_symm : symmetric t geom_incidence;
    geom_refl : reflexive t geom_incidence
  }.