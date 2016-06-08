Require Import CT.Category.

Set Universe Polymorphism.



(** Product category. *)
Program Definition ProductCategory (C D : Category) : Category :=
  {| ob := (@ob C * @ob D);
     mor := fun x y => (mor (fst x) (fst y) * mor (snd x) (snd y))%type;
     comp := fun _ _ _ x y => (comp (fst x) (fst y), comp (snd x) (snd y));
     id := fun x => (id (fst x), id (snd x))
  |}.
Next Obligation.
  rewrite assoc.
  rewrite assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite assoc.
  rewrite assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite id_left.
  rewrite id_left.
  reflexivity.
Qed.
Next Obligation.
  rewrite id_right.
  rewrite id_right.
  reflexivity.
Qed.
