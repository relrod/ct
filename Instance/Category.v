Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.
Require Import Coq.Program.Tactics.

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

(* This is the category of Categories. :) *)
Program Definition Cat : Category :=
  {| ob := Category;
     mor := Functor;
     comp := @ComposeFunctor;
     id := @IdentityFunctor
  |}.
Next Obligation.
Proof.
  apply F_eq. reflexivity. reflexivity.
Qed.
Next Obligation.
Proof.
  apply F_eq. reflexivity. reflexivity.
Qed.
Next Obligation.
  apply F_eq. reflexivity. reflexivity.
Qed.
Next Obligation.
  apply F_eq. reflexivity. reflexivity.
Qed.