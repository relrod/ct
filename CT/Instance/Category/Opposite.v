Require Import CT.Category.
Require Import CT.Instance.Category.FunctorCategory.
Require Import CT.Instance.Category.ProductCategory.

Set Universe Polymorphism.

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

Theorem op_preserves_functors :
  forall C D,
    (FunctorCategory C D)^op = FunctorCategory (C^op) (D^op).
Proof.
  admit.
Admitted.

Theorem op_preserves_products :
  forall C D,
    (ProductCategory C D)^op = ProductCategory (C^op) (D^op).
Proof.
  admit.
Admitted.
