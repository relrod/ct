Require Import CT.Category.

(** The opposite category for a category. *)
Program Definition Op (C : Category) : Category :=
  {| ob := @ob C;
     mor := fun a b => mor b a;
     comp := fun _ _ _ f g => comp g f;
     id := fun a => @id C a;
     assoc := fun _ _ _ _ _ _ _ => @assoc_sym _ _ _ _ _ _ _ _;
     assoc_sym := fun _ _ _ _ _ _ _ => @assoc _ _ _ _ _ _ _ _;
     id_left := fun _ _ => @id_right _ _ _;
     id_right := fun _ _ => @id_left _ _ _
  |}.

Notation "A '^op'" := (Op A) (at level 10).

Theorem c_op_op_is_c :
  forall C, C^op^op = C.
Proof.
  trivial.
Qed.
