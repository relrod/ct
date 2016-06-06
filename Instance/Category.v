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