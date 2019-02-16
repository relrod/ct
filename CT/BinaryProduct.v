Require Import CT.Category.

Set Universe Polymorphism.

(** * Binary products

as per https://ncatlab.org/nlab/show/cartesian+product
*)
Record BinaryProduct {C : Category} (x1 x2 : @ob C) :=
  { x1x2 : @ob C;

    (* Projections *)
    p1 : mor x1x2 x1;
    p2 : mor x1x2 x2;

    (* Laws that make a product a product *)
    bin_prod_mor :
      forall (Q : @ob C) (Qp1 : mor Q x1) (Qp2 : mor Q x2),
        mor Q x1x2;

    bin_prod_comp1 :
      forall (Q : @ob C) (Qp1 : mor Q x1) (Qp2 : mor Q x2),
        comp (bin_prod_mor Q Qp1 Qp2) p1 = Qp1;

    bin_prod_comp2 :
      forall (Q : @ob C) (Qp1 : mor Q x1) (Qp2 : mor Q x2),
        comp (bin_prod_mor Q Qp1 Qp2) p2 = Qp2;

    bin_prod_unique :
      forall (Q : @ob C) (Qp1 : mor Q x1) (Qp2 : mor Q x2) (f g : mor Q x1x2),
        comp f p1 = Qp1 ->
        comp f p2 = Qp2 ->
        comp g p1 = Qp1 ->
        comp g p2 = Qp2 ->
        f = g
  }.

(** The type that must be satisfied to prove a category has binary products. *)
Definition has_products (C : Category) :=
  forall (a b : @ob C), BinaryProduct a b.