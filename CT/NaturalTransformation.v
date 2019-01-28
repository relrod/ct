Require Import Coq.Program.Tactics.
Require Import CT.Category.
Require Import CT.Functor.

(** * Natrual transformations between two functors F, G : A -> B.

A natural transformation is a family of arrows such that forall x in A,
F(x) -> G(x) is in B and forall f : x -> y in A, the following commutes:

#
<pre>
F(x) ---F(f)----> F(y)
 |                 |
nt_components x   nt_components y
 |                 |
 v                 v
G(x) ---G(f)----> G(y)
</pre>
#
*)
Record NaturalTransformation {A B : Category} (F G : Functor A B) :=
  { nt_components : forall x, mor B (F_ob F x) (F_ob G x);
    nt_commutes : forall x y (f : mor x y),
        comp (F_mor F f) (nt_components y) = comp (nt_components x) (F_mor G f);
    nt_commutes_sym : forall x y (f : mor x y),
        comp (nt_components x) (F_mor G f) = comp (F_mor F f) (nt_components y)
  }.

Arguments nt_components {_} {_} _ _ _, {_} {_} {_} {_} _.

(** Equivalence of natural transformations, by proof irrelevance *)
Theorem nt_eq : forall A B F G (N M : NaturalTransformation F G),
    @nt_components A B F G N = @nt_components A B F G M ->
    N = M.
Proof.
  intros.
  destruct N, M.
  simpl in *.
  subst.
  f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.