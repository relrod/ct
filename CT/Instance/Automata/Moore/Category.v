Require Import CT.Automata.Moore.
Require Import CT.Category.

(** * The category [Aut] of Moore automata.

Motivation: https://ncatlab.org/nlab/show/automaton
*)
Program Definition MooreCategory : Category :=
  {| ob := Moore;
     mor := MooreMorphism;
     comp := fun _ _ _ x y => MooreMorphism_composition x y;
     id := fun _ => MooreMorphism_identity;
     assoc := fun _ _ _ _ => MooreMorphism_assoc
  |}.
Next Obligation.
Proof. symmetry. apply MooreMorphism_assoc. Qed.
Next Obligation.
Proof.
  apply MooreMorphism_eq.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.
Next Obligation.
  apply MooreMorphism_eq.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.