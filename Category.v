Set Primitive Projections.

Class Category :=
  { ob : Type;
    mor : ob -> ob -> Type;
    comp : forall {a b c : ob}, mor a b -> mor b c -> mor a c;
    id : forall {a : ob}, mor a a;
    assoc : forall {a b c d : ob} (f : mor a b) (g : mor b c) (h : mor c d),
        comp f (comp g h) = comp (comp f g) h;
    id_laws : forall (a b : ob) (f : mor a b),
        comp id f = f /\ comp f id = f
  }.

Bind Scope category_scope with Category.
Bind Scope morphism_scope with mor.
Bind Scope object_scope with ob.

Arguments mor {_} _ _, _ _ _.

(* Needs Primitive Projections *)
Arguments id {_ _}, {_} _, _ _.

(* TODO: I need to figure out how this works.
   https://coq.inria.fr/refman/Reference-Manual021.html *)
Coercion ob : Category >-> Sortclass.