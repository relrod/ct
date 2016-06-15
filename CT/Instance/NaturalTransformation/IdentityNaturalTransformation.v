Require Import CT.Category.
Require Import CT.Functor.
Require Import CT.NaturalTransformation.

(** * The identity natural transforamtion...

... [I : F -> F] where [F : Functor C D], maps each [C]-object to the identity
morphism in [D].

It also acts as identity for vertical composition of natural transforamtions and
for the 2-category [Cat].
*)
Program Definition IdentityNaturalTransformation {A B : Category} (F : Functor A B) :
  NaturalTransformation F F :=
  {| nt_components := fun _ => id
  |}.
Next Obligation.
Proof.
  rewrite id_left.
  rewrite id_right.
  reflexivity.
Qed.
Next Obligation.
Proof.
  symmetry.
  apply IdentityNaturalTransformation_obligation_1.
Qed.
