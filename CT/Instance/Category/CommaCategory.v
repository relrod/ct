(* NOEXPORT *)
Require Import CT.Category.
Require Import CT.Functor.

Section CommaCategory.
  Variable (C D E : Category).
  Variable (f : Functor C E).
  Variable (g : Functor D E).

  Record CommaCategoryOb :=
    { comma_a : ob C;
      comma_b : ob D;
      comma_a_b : @mor E (F_ob f comma_a) (F_ob g comma_b)
    }.

  Record CommaCategoryMor (a b : CommaCategoryOb):=
    { comma_beta : @mor C (comma_a a) (comma_a b);
      comma_gamma : @mor D (comma_b a) (comma_b b);
      comma_mor_law :
        (comp (F_mor f comma_beta) (comma_a_b b)) =
        (comp (comma_a_b a) (F_mor g comma_gamma))
    }.
End CommaCategory.