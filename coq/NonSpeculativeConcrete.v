From Coq Require Import List.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import Relation.

Inductive store_has_no_poison : dv_store -> Prop :=
  | Store_Has_No_Poison : forall ls,
      (forall x, (ls x) <> Some DV_Poison) ->
      store_has_no_poison ls
.

Inductive frame_has_no_poison : frame -> Prop :=
  | Frame_Has_No_Poison : forall ls ic pbid v,
      store_has_no_poison ls ->
      frame_has_no_poison (Frame ls ic pbid v)
.

Inductive stack_has_no_poison : list frame -> Prop :=
  | Stack_Has_No_Poison : forall stk,
      (forall f, In f stk -> frame_has_no_poison f) ->
      stack_has_no_poison stk
.

Inductive has_no_poison : state -> Prop :=
  | Has_No_Poison : forall ic c cs pbid ls stk gs mdl,
      store_has_no_poison ls ->
      store_has_no_poison gs ->
      stack_has_no_poison stk ->
      has_no_poison
        (mk_state
          ic
          c
          cs
          pbid
          ls
          stk
          gs
          mdl
        )
.

(* TODO: s1 should not contain poison? *)
Inductive ns_step : state -> state -> Prop :=
  | NS_Step : forall s1 s2,
      step s1 s2 -> has_no_poison s2 -> ns_step s1 s2
.

Definition multi_ns_step := multi ns_step.

Lemma ns_step_soundness : forall s1 s2,
  ns_step s1 s2 -> step s1 s2.
Proof.
Admitted.

Lemma multi_ns_step_soundness : forall s1 s2,
  multi_ns_step s1 s2 -> multi_step s1 s2.
Proof.
Admitted.

Lemma ns_step_relative_completeness : forall s1 s2,
  safe_state ns_step s1 ->
  step s1 s2 ->
  ns_step s1 s2.
Proof.
Admitted.

Lemma multi_ns_step_relative_completeness : forall s1 s2,
  safe_state ns_step s1 ->
  multi_step s1 s2 ->
  multi_ns_step s1 s2.
Proof.
  intros s1 s2 Hsafe Hms.
  induction Hms as [s s' | s s' s''].
  {
    apply ns_step_relative_completeness with (s2 := s') in Hsafe; try assumption.
    apply multi_base.
    assumption.
  }
  {
    assert(Ls' : safe_state ns_step s').
    {
      apply safe_state_preserved_on_reachability with (s := s).
      { assumption. }
      { apply IHHms. assumption. }
    }
    apply IHHms in Hsafe.
    apply ns_step_relative_completeness with (s2 := s'') in Ls'; try assumption.
    apply multi_trans with (y := s'); assumption.
  }
Qed.
