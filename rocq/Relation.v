Definition relation (X: Type) : Type := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_base : forall (x y : X), R x y -> multi R x y
  | multi_trans : forall (x y z : X), multi R x y -> R y z -> multi R x z
.

Lemma relation_concat {X : Type} : forall (R : relation X) (x y z : X),
  (multi R) x y -> (multi R) y z -> (multi R) x z.
Proof.
  intros R x y z H1 H2.
  induction H2 as [y z | y y' z].
  {
    eapply multi_trans.
    { eassumption. }
    { assumption. }
  }
  {
    apply IHmulti in H1.
    eapply multi_trans.
    { eassumption. }
    { assumption. }
  }
Qed.
