(** * Synthetic Projective Geometry

Following the work outlined here:
  http://www.maths.ed.ac.uk/~aar/papers/beutel.pdf
*)

Require Import Coq.Relations.Relations.

(** ** Geometry

A geometry is a set together with a so-called "incidence" relation that is
symmetric and reflexive. That is, a set together with a tolerance relation
(https://en.wikipedia.org/wiki/Tolerance_relation)

Specifically in our case, it's a set (rather, a type), with a [Relation]
and proofs that the [Relation] is a tolerance relation.
*)

Record Geometry :=
  { geom_point : Type;
    geom_incidence : relation geom_point;
    geom_symm : symmetric geom_point geom_incidence;
    geom_refl : reflexive geom_point geom_incidence
  }.
