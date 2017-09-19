Record PartiallyOrderedSet {element : Type} :=
  { le : element -> element -> Prop;
    reflexive : forall a, le a a;
    transitive : forall a b c, le a b /\ le b c -> le a c;
    antisymmetric : forall a b, le a b /\ le b a -> a = b
  }.
