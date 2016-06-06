Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.

(** Note that Coq-related instances are in [Instance.Coq] so we don't introduce
    circular dependencies on Instance.Functor and Instance.Category here. **)

(** This is the category of Categories. :) *)
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

(** Product category. *)
Program Definition ProductCategory (C D : Category) : Category :=
  {| ob := (@ob C * @ob D);
     mor := fun x y => (mor (fst x) (fst y) * mor (snd x) (snd y))%type;
     comp := fun _ _ _ x y => (comp (fst x) (fst y), comp (snd x) (snd y));
     id := fun x => (id (fst x), id (snd x))
  |}.
Next Obligation.
  rewrite assoc.
  rewrite assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite assoc.
  rewrite assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite id_left.
  rewrite id_left.
  reflexivity.
Qed.
Next Obligation.
  rewrite id_right.
  rewrite id_right.
  reflexivity.
Qed.