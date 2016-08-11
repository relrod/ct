Require Import Coq.Program.Tactics.
Set Primitive Projections.

Record PointedSet {set : Type} :=
  { basepoint : set
  }.

(** * Point-preserving maps.

Let \((X, x)\) and \((Y, y)\) be pointed sets. Then a point-preserving map
between them is a function \(f : (X, x) \to (Y, y)\). That is, a function from
\(X \to Y\) such that \(f(x) = y\).
*)
Record PointPreservingMap {A B} (X : @PointedSet A) (Y : @PointedSet B) :=
  { point_pres_map : A -> B;
    point_pres_law : point_pres_map (basepoint X) = (basepoint Y)
  }.

(** Here's an alternative definition using Sigma types. *)
Definition PointedSet' := existT (fun basepoint':Type => basepoint').

(** And a proof that the two definitions are isomorphic. *)
Definition NonprimeToPrime {A} (x : @PointedSet A) := PointedSet' A (basepoint x).

Definition PrimeToNonprime (x : {basepoint' : Type & basepoint'}) : @PointedSet (projT1 x) :=
  {| basepoint := (projT2 x) |}.

Theorem id1 :
  forall A x,
    PrimeToNonprime (@NonprimeToPrime A x) = id x.
Proof.
  intros.
  reflexivity.
Qed.

Theorem id2 :
  forall x,
    NonprimeToPrime (PrimeToNonprime x) = id x.
Proof.
  intros.
  destruct x.
  reflexivity.
Qed.

(** * Composition of point-preserving maps. *)
Program Definition ppm_composition
        {T U V : Type}
        {A : @PointedSet T}
        {B : @PointedSet U}
        {C : @PointedSet V}
        (map1 : PointPreservingMap A B)
        (map2 : PointPreservingMap B C) :
  PointPreservingMap A C :=
  {| point_pres_map := fun a => (point_pres_map B C map2) ((point_pres_map A B map1) a) |}.
Next Obligation.
Proof.
  destruct A, B, C, map1, map2.
  simpl in *.
  rewrite point_pres_law0.
  assumption.
Qed.