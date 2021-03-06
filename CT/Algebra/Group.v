Require Import CT.Algebra.Magma.
Require Import CT.Algebra.Monoid.
Require Import CT.Algebra.Semigroup.
Require Import Setoid.

(** * Groups

A group is a monoid with inverses.
*)
Record Group {T : Type} :=
  { monoid :> @Monoid T;
    inverse : T -> T;
    gr_inverse_left : forall x : T, mu monoid (inverse x) x = one monoid;
    gr_inverse_right : forall x : T, mu monoid x (inverse x) = one monoid
  }.

Lemma group_unique_unop :
  forall {T} (G : @Group T) x y z,
    mu G x y = z -> x = mu G z (inverse G y).
  intros.
  rewrite <- H.
  rewrite <- semigroup_assoc.
  rewrite gr_inverse_right.
  rewrite monoid_right_one.
  reflexivity.
Qed.

Theorem group_identity_unique {T} (G : @Group T) e :
  (forall x, mu G x e = x) -> e = one G.
Proof.
  apply (monoid_identity_unique e).
Qed.

Theorem group_inverse_inverse :
  forall {T} (G : @Group T) x,
    inverse G (inverse G x) = x.
Proof.
  intros.
  transitivity (mu G (inverse G (inverse G x)) (mu G (inverse G x) x)).
  rewrite gr_inverse_left.
  rewrite monoid_right_one.
  reflexivity.
  rewrite semigroup_assoc.
  rewrite gr_inverse_left.
  rewrite monoid_left_one.
  reflexivity.
Qed.

(**
Uniqueness of inverses. This proof is basically a replica of Dummit and Foote.
*)
Theorem group_inverse_unique {T} (G : @Group T) c :
  forall a,
    mu G a c = one G ->
    mu G c a = one G ->
    inverse G a = c.
Proof.
  intros.
  assert (c = mu G c (one G)).
  rewrite monoid_right_one.
  trivial.
  assert (one G = mu G a (inverse G a)).
  rewrite gr_inverse_right.
  trivial.
  rewrite H2 in H1.
  rewrite semigroup_assoc in H1.
  rewrite H0 in H1.
  rewrite H1.
  rewrite monoid_left_one.
  trivial.
Qed.

(** Inverses over products.

This gives an ugly proof of \((ab)^{-1} = b^{-1}a^{-1}\).
*)
Theorem group_inverse_of_product {T} (G : @Group T) :
  forall a b,
    inverse G (mu G a b) = mu G (inverse G b) (inverse G a).
Proof.
  intros.
  assert (mu G (mu G a b) (inverse G (mu G a b)) = one G).
  apply gr_inverse_right.
  assert (mu G (mu G a b) (mu G (inverse G b) (inverse G a)) = one G).
  assert (mu G (mu G a b) (mu G (inverse G b) (inverse G a)) =
          mu G (mu G a (mu G b (inverse G b))) (inverse G a)).
  rewrite semigroup_assoc.
  rewrite semigroup_assoc.
  trivial.
  rewrite H0.
  rewrite gr_inverse_right.
  rewrite monoid_right_one.
  apply gr_inverse_right.
  rewrite <- (group_inverse_unique G (mu G a b) (mu G (inverse G b) (inverse G a))).
  rewrite group_inverse_inverse.
  trivial.
  rewrite semigroup_assoc.
  assert (mu G (mu G (mu G (inverse G b) (inverse G a)) a) b =
          mu G (mu G (inverse G b) (mu G (inverse G a) a)) b).
  rewrite semigroup_assoc.
  trivial.
  rewrite H1.
  rewrite gr_inverse_left.
  rewrite monoid_right_one.
  apply gr_inverse_left.
  assumption.
Qed.

(** * Cancellation Laws *)
Theorem group_cancel_left {T} (G : @Group T) :
  forall a u v,
    mu G a u = mu G a v <-> u = v.
Proof.
  intros.
  split.
  intros.
  assert (mu G (inverse G a) (mu G a u) = mu G (inverse G a) (mu G a v)).
  rewrite H.
  trivial.
  repeat rewrite semigroup_assoc in H0.
  rewrite gr_inverse_left in H0.
  repeat rewrite monoid_left_one in H0.
  assumption.
  intros.
  rewrite H.
  trivial.
Qed.

Theorem group_cancel_right {T} (G : @Group T) :
  forall a u v,
    mu G u a = mu G v a <-> u = v.
Proof.
  intros.
  split.
  intros.
  assert (mu G (mu G u a) (inverse G a) = mu G (mu G v a) (inverse G a)).
  rewrite H.
  trivial.
  repeat rewrite <- semigroup_assoc in H0.
  rewrite gr_inverse_right in H0.
  repeat rewrite monoid_right_one in H0.
  assumption.
  intros.
  rewrite H.
  trivial.
Qed.

(** If \(x^2 = x\) then \(x = e\). *)
Theorem group_squared_identity {T} (G : @Group T) :
  forall x, mu_power G x 2 = x -> x = one G.
Proof.
  intros.
  simpl in H.
  rewrite monoid_right_one in H.
  rewrite <- (group_cancel_right G (inverse G x)) in H.
  rewrite <- semigroup_assoc in H.
  rewrite gr_inverse_right in H.
  rewrite monoid_right_one in H.
  assumption.
Qed.

(** \(ab = ba\) iff \(aba^{-1} = b\) *)
Theorem group_commutative_conj {T} (G : @Group T) :
  forall a b,
    mu G a b = mu G b a <-> mu G a (mu G b (inverse G a)) = b.
Proof.
  intros.
  split.
  intros.
  rewrite semigroup_assoc.
  rewrite H.
  rewrite <- semigroup_assoc.
  rewrite gr_inverse_right.
  trivial.
  intros.
  rewrite <- H.
  assert (mu G (mu G a (mu G b (inverse G a))) a =
          mu G a (mu G b (mu G (inverse G a) a))).
  rewrite <- semigroup_assoc.
  rewrite <- semigroup_assoc.
  auto.
  rewrite H0.
  rewrite gr_inverse_left.
  rewrite H.
  rewrite monoid_right_one.
  trivial.
Qed.

Theorem ab_e_is_ba_e {T} (G : @Group T) :
    forall a b,
      mu G a b = one G -> mu G b a = one G.
Proof.
  intros.
  rewrite <- (group_cancel_left G a).
  rewrite semigroup_assoc.
  rewrite monoid_identity_commutes.
  rewrite group_cancel_right.
  assumption.
Qed.

(* Possibly separate this out at some point. *)

(** * Group homomorphisms.

...are exactly the same as magma homomorphisms.
*)
Definition GroupHomomorphism {A B} (M : @Group A) (N : @Group B) :=
  @MagmaHomomorphism A B M N.

(** * Composition of maps. *)
Program Definition group_hom_composition
        {T U V : Type}
        {A : @Group T}
        {B : @Group U}
        {C : @Group V}
        (map1 : GroupHomomorphism A B)
        (map2 : GroupHomomorphism B C) :
  GroupHomomorphism A C
  := magma_hom_composition map1 map2.

(** * Equality of maps, assuming proof irrelevance. *)
Program Definition group_hom_eq
        {A B : Type}
        {F : @Group A}
        {G : @Group B}
        (N M : GroupHomomorphism F G) :
    @magma_hom A B F G N = @magma_hom A B F G M ->
    N = M
  := magma_hom_eq A B F G N M.

(** * Associativity of composition of maps. *)
Program Definition group_hom_composition_assoc
        {T : Type}
        {A B C D : @Group T}
        (f : GroupHomomorphism A B)
        (g : GroupHomomorphism B C)
        (h : GroupHomomorphism C D) :
  group_hom_composition f (group_hom_composition g h) =
  group_hom_composition (group_hom_composition f g) h
  := magma_hom_composition_assoc f g h.

(** * Identity map. *)
Program Definition group_hom_id
        {A : Type}
        {M : @Group A} :
  GroupHomomorphism M M :=
  magma_hom_id.


(** * Preservation of identity.

This is something we need to show because it's kind of a "happy accident"
that magma homomorphisms work as group homomorphisms.
*)
Theorem group_hom_pres_id {T U : Type} (A : @Group T) (B : @Group U) :
  forall (f : GroupHomomorphism A B) (a : T),
    magma_hom A B f (one A) = one B.
Proof.
  intros.
  assert (magma_hom A B f (one A) = magma_hom A B f (mu A (one A) (one A))).
  rewrite monoid_right_one. trivial.
  rewrite magma_hom_law in H.
  apply f_equal with
    (f := fun t => mu B (inverse B (magma_hom A B f (one A))) t) in H.
  rewrite gr_inverse_left in H.
  rewrite semigroup_assoc in H.
  rewrite gr_inverse_left in H.
  rewrite monoid_left_one in H.
  symmetry in H.
  apply H.
Qed.

(** If \(ab = 1\), then necessarily \(ba=1\) as well. *)
Lemma group_commutative_one {T} {G : @Group T} :
  forall a b, mu G a b = one G -> mu G b a = one G.
Proof.
  intros.
  apply f_equal with (f := fun t => mu G b t) in H.
  rewrite semigroup_assoc in H.
  rewrite monoid_identity_commutes in H.
  rewrite group_cancel_right in H.
  trivial.
Qed.

(** Given \(a \in G\) with \(ab = 1\), \(b\) must be the inverse to \(a\). *)
Lemma group_equals_one_implies_inverse {T : Type} (A : @Group T) (g : T) :
  forall x,
    mu A g x = one A -> x = inverse A g.
Proof.
  intros.
  assert (mu A g (inverse A g) = one A).
  apply gr_inverse_right.
  assert (mu A g x = mu A x g).
  rewrite H.
  rewrite group_commutative_one.
  trivial.
  trivial.
  assert (mu A x g = one A).
  apply group_commutative_one.
  trivial.
  symmetry.
  apply (group_inverse_unique A x g H H2).
Qed.

(** * Preservation of inverses.

This can now be shown by making use of [group_hom_pres_id].
*)
Theorem group_hom_pres_inverse {T U : Type} (A : @Group T) (B : @Group U) :
  forall (f : GroupHomomorphism A B) (a : T),
    magma_hom A B f (inverse A a) = inverse B (magma_hom A B f a).
Proof.
  intros.
  assert (mu B (magma_hom A B f a) (magma_hom A B f (inverse A a)) =
          magma_hom A B f (mu A a (inverse A a))).
  rewrite magma_hom_law.
  trivial.
  rewrite gr_inverse_right in H.
  rewrite group_hom_pres_id in H.
  apply group_equals_one_implies_inverse in H.
  assumption.
  assumption.
Qed.