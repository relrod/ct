Require Import CT.Category.
Require Import Coq.Program.Tactics.

(* This is the category of Coq 'Type's. *)
Program Instance CoqType : Category :=
  { ob := Type;
    mor := fun a b => a -> b;
    comp := fun a b c (f : a -> b) (g : b -> c) x => g (f x);
    id := fun _ => fun x => x
  }.

(* This is the category of Coq 'Prop's. *)
Program Instance CoqProp : Category :=
  { ob := Prop;
    mor := fun a b => a -> b;
    comp := fun a b c (f : a -> b) (g : b -> c) x => g (f x);
    id := fun _ => fun x => x
  }.

(* This is the category of Coq 'Set's. *)
Program Instance CoqSet : Category :=
  { ob := Set;
    mor := fun a b => a -> b;
    comp := fun a b c (f : a -> b) (g : b -> c) x => g (f x);
    id := fun _ => fun x => x
  }.