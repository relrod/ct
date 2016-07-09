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