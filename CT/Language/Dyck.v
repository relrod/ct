(** Dyck Language

This module is just a lightweight toy implementation of the Dyck language, just
for messing around. It isn't per-se related to category theory, although later
on we can formalize some things in relation to the bicyclic semigroup and the
Dyck syntactic monoid, if we get that far.

https://en.wikipedia.org/wiki/Dyck_language
*)

Require Import Coq.Lists.List.
Import ListNotations.

(* A Dyck word consists of only parentheses. *)
Inductive paren := l | r.

(* In fact, it is a list of parentheses. *)
Definition word := list paren.

Inductive Dyck : word -> Prop :=
| dEpsilon : Dyck nil
| dInd : forall w x, Dyck w -> Dyck x -> Dyck ([l] ++ w ++ [r] ++ x).

(*
Would like to use this definition instead, which is the direct CFG definition
of the Dyck language, but need to fiugre out how to make it play nice with
[dyck_must_start_l] below. The [dConcat] case is evil.

Inductive Dyck : word -> Prop :=
| dEpsilon : Dyck nil
| dParen : forall w, Dyck w -> Dyck ([l] ++ w ++ [r])
| dConcat : forall w x, Dyck w -> Dyck x -> Dyck (w ++ x).
*)

Example l_r_ex : Dyck ([l; r]).
Proof.
  apply (dInd [] []).
  apply dEpsilon.
  apply dEpsilon.
Qed.

(* Every Dyck word must start with a left paren. *)
Theorem dyck_must_start_l : forall w,
    Dyck w ->
      match w with
      | nil => True
      | cons c _ => c = l
      end.
Proof.
  intros.
  induction H.
  trivial.
  simpl.
  trivial.
Qed.
