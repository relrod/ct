Require Import CT.Automata.Mealy.
Require Import CT.Category.

(** * The category of mealy automata.

Motivation: Modification of https://ncatlab.org/nlab/show/automaton
*)
Program Definition MealyCategory : Category :=
  {| ob := Mealy;
     mor := MealyMorphism;
     comp := fun _ _ _ x y => MealyMorphism_composition x y;
     id := fun _ => MealyMorphism_identity;
     assoc := fun _ _ _ _ => MealyMorphism_assoc
  |}.
Next Obligation.
Proof. symmetry. apply MealyMorphism_assoc. Qed.
Next Obligation.
Proof.
  apply MealyMorphism_eq.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.
Next Obligation.
  apply MealyMorphism_eq.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.