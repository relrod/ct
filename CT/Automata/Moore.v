Require Import Coq.Program.Tactics.
Require Import ProofIrrelevance.

Section Moore.
  Record Moore :=
    { Q : Type;
      Sigma : Type;
      Y : Type;
      q0 : Q;
      delta : Sigma * Q -> Q;
      y : Q -> Y
    }.

  Record MooreMorphism (a b : Moore) :=
    { f_Q : (Q a) -> (Q b);
      f_Sigma : (Sigma a) -> (Sigma b);
      f_Y : (Y a) -> (Y b);
      pres_transition :
        forall sigma q,
          (delta b) (f_Sigma sigma, f_Q q) = f_Q ((delta a) (sigma, q));
      pres_outputs :
        forall q,
          f_Y ((y a) q) = (y b) (f_Q q);
      pres_init_state :
        f_Q (q0 a) = q0 b
    }.

  (** * Moore machine morphisms compose. *)
  Program Definition MooreMorphism_composition
          {A B C : Moore}
          (map1 : MooreMorphism A B)
          (map2 : MooreMorphism B C) :
    MooreMorphism A C :=
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

  (** * Moore machine identity morphisms hold. *)
  Program Definition MooreMorphism_identity
          {A : Moore} :
    MooreMorphism A A :=
    {| f_Q := fun a => a;
       f_Sigma := fun a => a;
       f_Y := fun a => a
    |}.

  (** * Equality of Moore morphisms, assuming proof irrelevance. *)
  Theorem MooreMorphism_eq : forall A B (N M : MooreMorphism A B),
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

  (** * Composition of Moore morphism is associative. *)
  Program Definition MooreMorphism_assoc
          {A B C D : Moore}
          (f : MooreMorphism A B)
          (g : MooreMorphism B C)
          (h : MooreMorphism C D) :
    MooreMorphism_composition f (MooreMorphism_composition g h) =
    MooreMorphism_composition (MooreMorphism_composition f g) h.
  Proof.
    destruct f, g, h.
    simpl.
    apply MooreMorphism_eq.
    simpl.
    reflexivity.
    reflexivity.
    reflexivity.
  Qed.
End Moore.
