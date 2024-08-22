From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.

Set Default Goal Selector "!".

Definition total_map (A : Type) := string -> A.

Definition empty_map {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition update_map {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (empty_map v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (update_map m x v)
                              (at level 100, v at next level, right associativity).

Lemma apply_empty_map : forall (A : Type) (x : string) (v : A),
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
  rewrite eqb_refl.
  reflexivity.
Qed.

Theorem update_map_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H.
  unfold update_map.
  apply eqb_neq in H.
  rewrite H.
  reflexivity.
Qed.
