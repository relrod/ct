Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Monoid.
Require Import CT.NaturalTransformation.
Require Import CT.Instance.Functor.
Require Import CT.Instance.NaturalTransformation.

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

(** The category for a given monoid. A monoid is exactly a category with one
    object.
 *)
Program Definition MonoidCategory {T} (M : Monoid) : Category :=
  {| ob := unit;
     mor := fun _ _ => T;
     comp := fun _ _ _ => mu M;
     id := fun a => one M;
  |}.
Next Obligation.
Proof. apply monoid_assoc. Qed.
Next Obligation.
Proof. rewrite <- monoid_assoc. reflexivity. Qed.
Next Obligation.
Proof. rewrite monoid_left_one. reflexivity. Qed.
Next Obligation.
Proof. rewrite monoid_right_one. reflexivity. Qed.

Program Definition FunctorCategory (C D : Category) : Category :=
  {| ob := Functor C D;
     mor := NaturalTransformation;
     id := IdentityNaturalTransformation;
     comp := @CompositionNaturalTransformation C D
  |}.
Next Obligation.
Proof.
  apply nt_eq.
  rewrite CompositionNaturalTransformation_assoc.
  reflexivity.
Qed.
Next Obligation.
Proof.
  rewrite CompositionNaturalTransformation_assoc.
  reflexivity.
Qed.
Next Obligation.
Proof. apply CompositionNaturalTransformation_id_left. Qed.
Next Obligation.
Proof. apply CompositionNaturalTransformation_id_right. Qed.