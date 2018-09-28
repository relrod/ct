Require Import Coq.Program.Tactics.
Require Import ProofIrrelevance.

Section Mealy.
  Record Mealy :=
    { Q : Type;
      Sigma : Type;
      Y : Type;
      q0 : Q;
      delta : Sigma * Q -> Q;
      y : Q * Sigma -> Y
    }.

  Record MealyMorphism (a b : Mealy) :=
    { f_Q : (Q a) -> (Q b);
      f_Sigma : (Sigma a) -> (Sigma b);
      f_Y : (Y a) -> (Y b);
      pres_transition :
        forall sigma q,
          (delta b) (f_Sigma sigma, f_Q q) = f_Q ((delta a) (sigma, q));
      pres_outputs :
        forall q sigma,
          f_Y ((y a) (q, sigma)) = (y b) (f_Q q, f_Sigma sigma);
      pres_init_state :
        f_Q (q0 a) = q0 b
    }.

  (** Mealy machine morphisms compose. *)
  Program Definition MealyMorphism_composition
          {A B C : Mealy}
          (map1 : MealyMorphism A B)
          (map2 : MealyMorphism B C) :
    MealyMorphism A C :=
    {| f_Q := fun a => (f_Q B C map2) ((f_Q A B map1) a);
       f_Sigma := fun a => (f_Sigma B C map2) ((f_Sigma A B map1) a);
       f_Y := fun a => (f_Y B C map2) ((f_Y A B map1) a);
    |}.
  Next Obligation.
  Proof.
    destruct map1, map2.
    simpl in *.
    rewrite pres_transition1.
    rewrite pres_transition0.
    reflexivity.
  Qed.
  Next Obligation.
    destruct map1, map2.
    simpl in *.
    rewrite pres_outputs0.
    rewrite pres_outputs1.
    reflexivity.
  Qed.
  Next Obligation.
    destruct map1, map2.
    simpl in *.
    rewrite pres_init_state0.
    rewrite pres_init_state1.
    reflexivity.
  Qed.

  (** Mealy machine identity morphisms hold. *)
  Program Definition MealyMorphism_identity
          {A : Mealy} :
    MealyMorphism A A :=
    {| f_Q := fun a => a;
       f_Sigma := fun a => a;
       f_Y := fun a => a
    |}.

  (** Equality of Mealy morphisms, assuming proof irrelevance. *)
  Theorem MealyMorphism_eq : forall A B (N M : MealyMorphism A B),
      @f_Q A B N = @f_Q A B M ->
      @f_Sigma A B N = @f_Sigma A B M ->
      @f_Y A B N = @f_Y A B M ->
      N = M.
  Proof.
    intros.
    destruct N, M.
    simpl in *.
    subst.
    f_equal;
      apply proof_irrelevance.
  Qed.

  (** Composition of Mealy morphism is associative. *)
  Program Definition MealyMorphism_assoc
          {A B C D : Mealy}
          (f : MealyMorphism A B)
          (g : MealyMorphism B C)
          (h : MealyMorphism C D) :
    MealyMorphism_composition f (MealyMorphism_composition g h) =
    MealyMorphism_composition (MealyMorphism_composition f g) h.
  Proof.
    destruct f, g, h.
    simpl.
    apply MealyMorphism_eq.
    simpl.
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.
End Mealy.
