Definition relation (X: Type) : Type := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_base : forall (x y : X), R x y -> multi R x y
  | multi_trans : forall (x y z : X), multi R x y -> R y z -> multi R x z
.
