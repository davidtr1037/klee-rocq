From Coq Require Import Bool.Bool.

From SE Require Import LLVMAst.

(* TODO: why is it needed? *)
Set Default Goal Selector "!".

Definition total_map (A : Type) := raw_id -> A.

Definition empty_map {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition update_map {A : Type} (m : total_map A) (x : raw_id) (v : A) :=
  fun y => if raw_id_eqb x y then v else m y.

Notation "'_' '!->' v" := (empty_map v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (update_map m x v)
                              (at level 100, v at next level, right associativity).

Lemma apply_empty_map : forall (A : Type) (x : raw_id) (v : A),
  (_ !-> v) x = v.
Proof.
  intros A x v.
  reflexivity.
Qed.

Lemma update_map_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold update_map.
  rewrite raw_id_eqb_refl.
  reflexivity.
Qed.

Theorem update_map_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H.
  unfold update_map.
  apply raw_id_eqb_neq in H.
  rewrite H.
  reflexivity.
Qed.

Inductive map_equiv {A : Type} : (total_map A) -> (total_map A) -> Prop :=
  | MapEquiv : forall m1 m2,
      (forall x, m1 x = m2 x) -> map_equiv m1 m2
.

Lemma map_equiv_symmetry : forall (A : Type) (m1 m2 : total_map A),
  (map_equiv m1 m2) <-> (map_equiv m2 m1).
Proof.
  intros A m1 m2.
  split; intros H.
  {
    apply MapEquiv.
    inversion H; subst.
    intros x.
    specialize (H0 x).
    symmetry.
    assumption.
  }
  {
    apply MapEquiv.
    inversion H; subst.
    intros x.
    specialize (H0 x).
    symmetry.
    assumption.
  }
Qed.

Lemma map_equiv_transitivity : forall (A : Type) (m1 m2 m3 : total_map A),
  (map_equiv m1 m2) -> (map_equiv m2 m3) -> (map_equiv m1 m3).
Proof.
  intros A m1 m2 m3 H1 H2.
  apply MapEquiv.
  inversion H1; subst.
  inversion H2; subst.
  intros x.
  specialize (H x).
  specialize (H0 x).
  rewrite H.
  assumption.
Qed.

Lemma map_equiv_same : forall (A : Type) (m : total_map A),
  map_equiv m m.
Proof.
  intros A m.
  apply MapEquiv.
  intros s.
  reflexivity.
Qed.

Fixpoint multi_update_map {A : Type} (m : total_map A) (l : list (prod raw_id A)) :=
  match l with
  | nil => m
  | (x, v) :: t => multi_update_map (x !-> v; m) t
  end
.

Lemma lemma_multi_update_map_1: forall (A : Type) (m1 m2 : total_map A) x l,
  m1 x = m2 x ->
  (multi_update_map m1 l) x = (multi_update_map m2 l) x.
Proof.
  intros A m1 m2 x l Heq.
  generalize dependent m2.
  generalize dependent m1.
  induction l as [ | (y, v) t].
  {
    intros m1 m2 Heq.
    simpl.
    assumption.
  }
  {
    intros m1 m2 Heq.
    simpl.
    apply IHt.
    destruct (raw_id_eqb y x) eqn:E.
    {
      apply raw_id_eqb_eq in E.
      rewrite E.
      rewrite update_map_eq, update_map_eq.
      reflexivity.
    }
    {
      apply raw_id_eqb_neq in E.
      rewrite update_map_neq, update_map_neq; try (assumption).
    }
  }
Qed.

Lemma lemma_multi_update_map_2: forall (A : Type) (m : total_map A) x y v l,
  x <> y ->
  (multi_update_map (x !-> v; m) l) y = (multi_update_map m l) y.
Proof.
  intros A m x y v l H.
  apply lemma_multi_update_map_1.
  rewrite update_map_neq.
  { reflexivity. }
  { assumption. }
Qed.

(* TODO: rename to map_equiv_override? *)
Lemma map_equiv_shadow: forall (A : Type) (m : total_map A) x v1 v2 l,
  map_equiv
    (x !-> v2; (multi_update_map (x !-> v1; m) l))
    (x !-> v2; (multi_update_map m l)).
Proof.
  intros A m x v1 v2 l.
  apply MapEquiv.
  intros y.
  destruct (raw_id_eqb x y) eqn:E.
  {
    apply raw_id_eqb_eq in E.
    rewrite E.
    rewrite update_map_eq, update_map_eq.
    reflexivity.
  }
  {
    apply raw_id_eqb_neq in E.
    rewrite update_map_neq, update_map_neq; try (assumption).
    apply lemma_multi_update_map_2.
    assumption.
  }
Qed.
