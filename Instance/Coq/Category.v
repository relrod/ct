Require Import CT.Category.

(* This is the category of Coq 'Type's. *)
Program Definition CoqType : Category :=
  {| ob := Type;
     mor := fun a b => a -> b;
     comp := fun a b c (f : a -> b) (g : b -> c) x => g (f x);
     id := fun _ => fun x => x
  |}.

(* This is the category of Coq 'Prop's. *)
Program Definition CoqProp : Category :=
  {| ob := Prop;
     mor := fun a b => a -> b;
     comp := fun a b c (f : a -> b) (g : b -> c) x => g (f x);
     id := fun _ => fun x => x
  |}.

(* This is the category of Coq 'Set's. *)
Program Definition CoqSet : Category :=
  {| ob := Set;
     mor := fun a b => a -> b;
     comp := fun a b c (f : a -> b) (g : b -> c) x => g (f x);
     id := fun _ => fun x => x
  |}.

