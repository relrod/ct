Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.Instance.Functor.ComposeFunctor.
Require Import CT.Instance.Functor.Endofunctor.
Require Import CT.Instance.Functor.FaithfulFunctor.
Require Import CT.Instance.Functor.FullFunctor.

Program Definition IdentityFunctor {C : Category} : @Endofunctor C :=
  {| F_ob := fun x => x;
     F_mor := fun _ _ f => f;
  |}.

(** The identity functor is always faithful. *)
Theorem identity_is_faithful (C : Category) : FaithfulFunctor (@IdentityFunctor C).
Proof.
  intro.
  simpl.
  trivial.
Qed.

(** The identity functor is always full. *)
Theorem identity_is_full (C : Category) : FullFunctor (@IdentityFunctor C).
Proof.
  repeat intro.
  exists f.
  simpl.
  reflexivity.
Qed.

(** Composition of [IdentityFunctor]s is still the [IdentityFunctor]. *)
Theorem comp_identity_identity :
  forall {C : Category} (F G : @Endofunctor C),
    F = @IdentityFunctor C ->
    G = @IdentityFunctor C ->
    ComposeFunctor F G = @IdentityFunctor C.
Proof.
  intros.
  unfold ComposeFunctor.
  subst.
  simpl.
  unfold IdentityFunctor at 5.
  apply F_eq;
    reflexivity.
Qed.