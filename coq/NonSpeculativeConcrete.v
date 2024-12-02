From Coq Require Import List.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Relation.

From SE.Utils Require Import IDMap.

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

Lemma store_has_no_poison_update : forall s x dv,
  store_has_no_poison s ->
  dv <> DV_Poison ->
  store_has_no_poison (x !-> Some dv; s).
Proof.
Admitted.

(* TODO: rename *)
Lemma stack_has_no_poison_suffix : forall f stk,
  stack_has_no_poison (f :: stk) -> stack_has_no_poison stk.
Proof.
  intros f stk H.
  inversion H; subst.
  apply Stack_Has_No_Poison.
  intros f' Hin.
  apply H0.
  apply in_cons.
  assumption.
Qed.

(* TODO: s1 should not contain poison? *)
Inductive ns_step : state -> state -> Prop :=
  | NS_Step : forall s1 s2,
      step s1 s2 -> has_no_poison s2 -> ns_step s1 s2
.

Definition multi_ns_step := multi ns_step.

(* TODO: is needed? *)
Lemma ns_step_soundness : forall s1 s2,
  ns_step s1 s2 -> step s1 s2.
Proof.
Admitted.

(* TODO: is needed? *)
Lemma multi_ns_step_soundness : forall s1 s2,
  multi_ns_step s1 s2 -> multi_step s1 s2.
Proof.
Admitted.

Lemma ns_step_relative_completeness : forall s1 s2,
  is_supported_state s1 ->
  safe_state ns_step s1 ->
  has_no_poison s1 ->
  step s1 s2 ->
  ns_step s1 s2.
Proof.
  intros s1 s2 His Hsafe Hnp Hstep.
  inversion Hnp; subst.
  inversion Hstep; subst.
  (* INSTR_Op *)
  {
    apply NS_Step.
    { eapply Step_OP; eassumption. }
    {
      apply Has_No_Poison; try assumption.
      apply store_has_no_poison_update; try assumption.
      admit.
    }
  }
  (* Phi *)
  {
    apply NS_Step.
    { eapply Step_Phi; eassumption. }
    {
      apply Has_No_Poison; try assumption.
      admit.
    }
  }
  (* TERM_UnconditionalBr *)
  {
    apply NS_Step.
    { eapply Step_UnconditionalBr; eassumption. }
    { apply Has_No_Poison; assumption. }
  }
  {
    apply NS_Step.
    { eapply Step_Br_True; eassumption. }
    { apply Has_No_Poison; assumption. }
  }
  {
    apply NS_Step.
    { eapply Step_Br_False; eassumption. }
    { apply Has_No_Poison; assumption. }
  }
  {
    apply NS_Step.
    { eapply Step_VoidCall; eassumption. }
    { admit. }
  }
  {
    apply NS_Step.
    { eapply Step_Call; eassumption. }
    { admit. }
  }
  {
    apply NS_Step.
    { eapply Step_RetVoid; eassumption. }
    {
      inversion H1; subst.
      apply Has_No_Poison; try assumption.
      {
        assert(L : frame_has_no_poison (Frame ls' ic' pbid' None)).
        { apply H2. apply in_eq. }
        inversion L; subst.
        assumption.
      }
      {
        eapply stack_has_no_poison_suffix.
        eassumption.
      }
    }
  }
  {
    apply NS_Step.
    { eapply Step_Ret; eassumption. }
    { admit. }
  }
  {
    apply NS_Step.
    { eapply Step_MakeSymbolicInt32; eassumption. }
    {
      apply Has_No_Poison; try assumption.
      apply Store_Has_No_Poison.
      inversion H; subst.
      intros x.
      destruct (raw_id_eqb x v) eqn:E.
      {
        rewrite raw_id_eqb_eq in E.
        rewrite E.
        rewrite update_map_eq.
        intros Hf.
        discriminate Hf.
      }
      {
        rewrite raw_id_eqb_neq in E.
        rewrite update_map_neq.
        { apply H2. }
        { symmetry. assumption. }
      }
    }
  }
  {
    apply NS_Step.
    { eapply Step_Assume; eassumption. }
    { apply Has_No_Poison; try assumption. }
  }
Admitted.

Lemma multi_ns_step_relative_completeness : forall s1 s2,
  is_supported_state s1 ->
  safe_state ns_step s1 ->
  has_no_poison s1 ->
  multi_step s1 s2 ->
  multi_ns_step s1 s2.
Proof.
  intros s1 s2 His Hnp Hsafe Hms.
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
      { apply IHHms; assumption. }
    }
    apply IHHms in Hsafe.
    {
      apply ns_step_relative_completeness with (s2 := s'') in Ls'; try assumption.
      { apply multi_trans with (y := s'); try assumption. }
      { apply is_supported_multi_step with (s := s); assumption. }
      { admit. }
    }
    { assumption. }
    { assumption. }
  }
Admitted.
