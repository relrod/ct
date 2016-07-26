Require Import Coq.Program.Tactics.
Set Primitive Projections.
Set Universe Polymorphism.

(** * Categories

The definition of category can be found in any introductory category theory text
or on ncatlab.

The interesting thing to note is that objects here are values of the universe
[Type], morphisms are functions between those values, and the axioms are encoded
as fields of the [Category] record and must be proven when a [Category] is
created.
*)
Record Category :=
  { ob : Type;
    mor : ob -> ob -> Type;
    comp : forall {a b c : ob}, mor a b -> mor b c -> mor a c;
    id : forall {a : ob}, mor a a;
    assoc : forall {a b c d : ob} (f : mor a b) (g : mor b c) (h : mor c d),
        comp f (comp g h) = comp (comp f g) h;
    assoc_sym : forall {a b c d : ob} (f : mor a b) (g : mor b c) (h : mor c d),
        comp (comp f g) h = comp f (comp g h);
    id_left : forall (a b : ob) (f : mor a b), comp id f = f;
    id_right : forall (a b : ob) (f : mor a b), comp f id = f
  }.

Bind Scope category_scope with Category.
Bind Scope morphism_scope with mor.
Bind Scope object_scope with ob.

Arguments mor {_} _ _, _ _ _.
Arguments comp {_ _ _ _} _ _, _ _ _ _ _ _.
Arguments ob {_}, _.

(* Needs Primitive Projections *)
Arguments id {_ _}, {_} _, _ _.

(* TODO: I need to figure out how this works.
   https://coq.inria.fr/refman/Reference-Manual021.html *)
Coercion ob : Category >-> Sortclass.
