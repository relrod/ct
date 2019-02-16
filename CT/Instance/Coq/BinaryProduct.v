Require Import CT.BinaryProduct.
Require Import CT.Category.
Require Import CT.Instance.Coq.Category.
Require Import FunctionalExtensionality.

Program Definition CoqType_product (a b : @ob CoqType) : BinaryProduct a b :=
  {| x1x2 := (a * b)%type;
     p1 := fst;
     p2 := snd;
     bin_prod_mor := fun _ a b c => (a c, b c)
  |}.
Proof.
  Next Obligation.
  extensionality q.
  apply (fun p => equal_f p q) in H1.
  apply (fun p => equal_f p q) in H2.
  simpl in *.
  destruct (f q), (g q).
  cbn in H1, H2.
  subst.
  trivial.
Qed.

Theorem CoqType_has_products : has_products CoqType.
Proof.
  unfold has_products.
  intros.
  apply CoqType_product.
Qed.

Program Definition CoqProp_product (a b : @ob CoqProp) : BinaryProduct a b :=
  {| x1x2 := (a * b)%type;
     p1 := fst;
     p2 := snd;
     bin_prod_mor := fun _ a b c => (a c, b c)
  |}.
Proof.
  Next Obligation.
  extensionality q.
  apply (fun p => equal_f p q) in H1.
  apply (fun p => equal_f p q) in H2.
  simpl in *.
  destruct (f q), (g q).
  cbn in H1, H2.
  subst.
  trivial.
Qed.

Theorem CoqProp_has_products : has_products CoqProp.
Proof.
  unfold has_products.
  intros.
  apply CoqProp_product.
Qed.

Program Definition CoqSet_product (a b : @ob CoqSet) : BinaryProduct a b :=
  {| x1x2 := (a * b)%type;
     p1 := fst;
     p2 := snd;
     bin_prod_mor := fun _ a b c => (a c, b c)
  |}.
Proof.
  Next Obligation.
  extensionality q.
  apply (fun p => equal_f p q) in H1.
  apply (fun p => equal_f p q) in H2.
  simpl in *.
  destruct (f q), (g q).
  cbn in H1, H2.
  subst.
  trivial.
Qed.

Theorem CoqSet_has_products : has_products CoqSet.
Proof.
  unfold has_products.
  intros.
  apply CoqSet_product.
Qed.
