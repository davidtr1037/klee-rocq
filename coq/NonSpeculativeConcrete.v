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

Lemma has_no_poison_store_update : forall s x dv,
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

Lemma has_no_poison_init_state : forall mdl fid s,
  init_state mdl fid = Some s ->
  has_no_poison s.
Proof.
Admitted.

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

Lemma has_no_poison_eval_exp : forall ls gs ot e dv,
  is_supported_exp e ->
  eval_exp ls gs ot e = Some dv ->
  dv <> DV_Poison.
Proof.
Admitted.

Lemma has_no_poison_eval_phi_args : forall ls gs t args pbid dv,
  (forall bid e, In (bid, e) args -> is_supported_exp e) ->
  eval_phi_args ls gs t args pbid = Some dv ->
  dv <> DV_Poison.
Proof.
Admitted.

Lemma has_no_poison_step : forall s1 s2,
  is_supported_state s1 ->
  safe_state ns_step s1 ->
  has_no_poison s1 ->
  step s1 s2 ->
  has_no_poison s2.
Proof.
  intros s1 s2 His Hsafe Hnp Hstep.
  inversion His; subst.
  inversion Hnp; subst.
  inversion Hstep; subst.
  (* INSTR_Op *)
  {
    apply Has_No_Poison; try assumption.
    apply has_no_poison_store_update; try assumption.
    inversion H; subst.
    { eapply has_no_poison_eval_exp; eassumption. }
    (* UDiv *)
    {
      simpl in H14.
      destruct
        (eval_exp ls gs (Some t) e1) as [dv1 | ] eqn:E1,
        (eval_exp ls gs (Some t) e2) as [dv2 | ] eqn:E2;
      try discriminate H14.
      unfold eval_ibinop in H14.
      destruct dv1 as [di1 | | ] eqn:Edv1, dv2 as [di2 | | ] eqn:Edv2;
      try (discriminate H14);
      try (destruct di1; discriminate H14).
      destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2];
      try discriminate H14.
      {
        simpl in H14.
        destruct (BinInt.Z.eqb (Int1.unsigned n2) BinNums.Z0) eqn:E; subst.
        { discriminate H14. }
        {
          inversion H14. subst.
          intros Hf.
          discriminate Hf.
        }
      }
      (* TODO: these are similar... *)
      { admit. }
      { admit. }
      { admit. }
      { admit. }
    }
  }
  (* Phi *)
  {
    apply Has_No_Poison; try assumption.
    apply has_no_poison_store_update; try assumption.
    eapply has_no_poison_eval_phi_args.
    { inversion H; subst. eassumption. }
    { eassumption. }
  }
  (* TERM_UnconditionalBr *)
  {
    apply Has_No_Poison; assumption.
  }
  {
    apply Has_No_Poison; assumption.
  }
  {
    apply Has_No_Poison; assumption.
  }
  {
    admit.
  }
  {
    admit.
  }
  {
    apply Has_No_Poison; try assumption.
    {
      assert(L : frame_has_no_poison (Frame ls' ic' pbid' None)).
      {
        inversion H12; subst.
        eapply H2.
        apply in_eq.
      }
      { inversion L; subst. assumption. }
    }
    {
      eapply stack_has_no_poison_suffix.
      eassumption.
    }
  }
  {
    apply Has_No_Poison; try assumption.
    {
      apply has_no_poison_store_update.
      {
        assert(L : frame_has_no_poison (Frame ls' ic' pbid' (Some v))).
        {
          inversion H12; subst.
          eapply H2.
          apply in_eq.
        }
        inversion L; subst.
        assumption.
      }
      {
        eapply has_no_poison_eval_exp.
        { inversion H; subst. eassumption. }
        { eassumption. }
      }
    }
    {
      eapply stack_has_no_poison_suffix.
      eassumption.
    }
  }
  {
    apply Has_No_Poison; try assumption.
    apply Store_Has_No_Poison.
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
      { inversion H5; subst. apply H2. }
      { symmetry. assumption. }
    }
  }
  {
    apply Has_No_Poison; try assumption.
  }
Admitted.

Lemma has_no_poison_multi_step : forall s1 s2,
  is_supported_state s1 ->
  safe_state ns_step s1 ->
  has_no_poison s1 ->
  multi_step s1 s2 ->
  has_no_poison s2.
Proof.
Admitted.

(* TODO: use has_no_poison_step *)
Lemma ns_step_relative_completeness : forall s1 s2,
  is_supported_state s1 ->
  safe_state ns_step s1 ->
  has_no_poison s1 ->
  step s1 s2 ->
  ns_step s1 s2.
Proof.
  intros s1 s2 His Hsafe Hnp Hstep.
  apply NS_Step.
  { assumption. }
  { apply has_no_poison_step with (s1 := s1); try assumption. }
Qed.

Lemma multi_ns_step_relative_completeness : forall s1 s2,
  is_supported_state s1 ->
  safe_state ns_step s1 ->
  has_no_poison s1 ->
  multi_step s1 s2 ->
  multi_ns_step s1 s2.
Proof.
  intros s1 s2 His Hsafe Hnp Hms.
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
    apply multi_trans with (y := s').
    { apply IHHms; assumption. }
    {
      apply ns_step_relative_completeness with (s2 := s'') in Ls'; try assumption.
      { apply is_supported_multi_step with (s := s); assumption. }
      { apply has_no_poison_multi_step with (s1 := s); try assumption. }
    }
  }
Qed.
