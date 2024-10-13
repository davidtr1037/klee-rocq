From Coq Require Import List.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import ChoiceAxiom.
From SE Require Import Completeness.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

From SE.Utils Require Import IDMap.

Inductive tree (X : Type) : Type :=
  | t_leaf (x : X)
  | t_subtree (x : X) (l : list (tree X))
.

Arguments t_leaf {X}.
Arguments t_subtree {X}.

Definition root {X : Type} (t : tree X) : X :=
  match t with
  | t_leaf x => x
  | t_subtree x _ => x
  end
.

Arguments root {X}.

Definition execution_tree := tree sym_state.

Inductive equiv_smt_store : smt_store -> smt_store -> Prop :=
  | EquivSMTStore : forall (s1 s2 : smt_store),
      (forall x,
        ((s1 x) = None /\ (s2 x) = None) \/
        (exists se1 se2, (s1 x) = Some se1 /\ (s2 x) = Some se2 /\ equiv_smt_expr se1 se2)
      ) -> equiv_smt_store s1 s2
.

Lemma equiv_smt_store_refl : forall s,
  equiv_smt_store s s.
Proof.
  intros s.
  apply EquivSMTStore.
  intros x.
  destruct (s x) as [se | ] eqn:E.
  {
    right.
    exists se, se.
    split; try reflexivity.
    split; try reflexivity.
    apply equiv_smt_expr_refl.
  }
  { left. split; reflexivity. }
Qed.

Lemma equiv_smt_store_symmetry : forall s1 s2,
  equiv_smt_store s1 s2 -> equiv_smt_store s2 s1.
Proof.
  intros s1 s2 Heq.
  inversion Heq; subst.
  apply EquivSMTStore.
  intros x.
  specialize (H x).
  destruct H as [H | H].
  {
    destruct H as [H_1 H_2].
    left.
    split; assumption.
  }
  {
    destruct H as [se1 [se2 [H_1 [H_2 H_3]]]].
    right.
    exists se2, se1.
    split; try assumption.
    split; try assumption.
    apply equiv_smt_expr_symmetry.
    assumption.
  }
Qed.

Lemma equiv_smt_store_transitivity : forall s1 s2 s3,
  equiv_smt_store s1 s2 -> equiv_smt_store s2 s3 -> equiv_smt_store s1 s3.
Proof.
  intros s1 s2 s3 Heq1 Heq2.
  inversion Heq1; subst.
  inversion Heq2; subst.
  apply EquivSMTStore.
  intros x.
  specialize (H x).
  destruct H as [H | H].
  {
    destruct H as [H_1 H_2].
    left.
    specialize (H0 x).
    destruct H0 as [H0 | H0].
    {
      destruct H0 as [H0_1 H0_2].
      split; try assumption.
    }
    {
      destruct H0 as [se1 [se2 [H0_1 [H0_2 H0_3]]]].
      rewrite H_2 in H0_1.
      discriminate H0_1.
    }
  }
  {
    destruct H as [se1 [se2 [H_1 [H_2 H_3]]]].
    specialize (H0 x).
    destruct H0 as [H0 | H0].
    {
      destruct H0 as [H0_1 H0_2].
      rewrite H_2 in H0_1.
      discriminate H0_1.
    }
    {
      destruct H0 as [se2' [se3 [H0_1 [H0_2 H0_3]]]].
      right.
      rewrite H0_1 in H_2.
      inversion H_2; subst.
      exists se1, se3.
      split; try assumption.
      split; try assumption.
      apply equiv_smt_expr_transitivity with (e2 := se2); assumption.
    }
  }
Qed.

Lemma equiv_empty_smt_store : equiv_smt_store empty_smt_store empty_smt_store.
Proof.
  apply EquivSMTStore.
  intros x.
  left.
  split; (unfold empty_smt_store; rewrite apply_empty_map; reflexivity).
Qed.

Lemma equiv_smt_store_update : forall s1 s2 v se1 se2,
  equiv_smt_store s1 s2 ->
  equiv_smt_expr se1 se2 ->
  equiv_smt_store (v !-> Some se1; s1) (v !-> Some se2; s2).
Proof.
  intros s1 s2 v se1 se2 Hs He.
  apply EquivSMTStore.
  intros x.
  inversion Hs; subst.
  specialize (H x).
  destruct (raw_id_eqb v x) eqn:E.
  {
    rewrite raw_id_eqb_eq in E.
    rewrite E.
    rewrite update_map_eq, update_map_eq.
    right.
    exists se1, se2.
    split; try reflexivity;
    split; try reflexivity.
    assumption.
  }
  {
    rewrite raw_id_eqb_neq in E.
    rewrite update_map_neq, update_map_neq; try assumption.
  }
Qed.

Lemma equiv_sym_eval_exp : forall ls1 gs1 ls2 gs2 ot e se1,
  is_supported_exp e ->
  equiv_smt_store ls1 ls2 ->
  equiv_smt_store gs1 gs2 ->
  sym_eval_exp ls1 gs1 ot e = Some se1 ->
  (exists se2, (sym_eval_exp ls2 gs2 ot e) = Some se2 /\ equiv_smt_expr se1 se2).
Proof.
  intros ls1 gs1 ls2 gs2 ot e se1 His Heq1 Heq2 Heval.
  generalize dependent se1.
  generalize dependent ot.
  induction e; intros ot se1 Heval; simpl in Heval; try inversion His; subst.
  {
    unfold sym_lookup_ident in Heval.
    destruct id as [x | x] eqn:E.
    {
      inversion Heq2; subst.
      specialize (H x).
      destruct H as [[H_1 H_2]| H].
      { rewrite Heval in H_1. discriminate H_1. }
      {
        destruct H as [se1' [se2 [H_1 [H_2 H_3]]]].
        rewrite H_1 in Heval.
        inversion Heval; subst.
        exists se2.
        split.
        { simpl. assumption. }
        { assumption. }
      }
    }
    {
      inversion Heq1; subst.
      specialize (H x).
      destruct H as [[H_1 H_2]| H].
      { rewrite Heval in H_1. discriminate H_1. }
      {
        destruct H as [se1' [se2 [H_1 [H_2 H_3]]]].
        rewrite H_1 in Heval.
        inversion Heval; subst.
        exists se2.
        split.
        { simpl. assumption. }
        { assumption. }
      }
    }
  }
  {
    exists se1.
    split.
    { simpl. assumption. }
    { apply equiv_smt_expr_refl. }
  }
  {
    destruct (sym_eval_exp ls1 gs1 (Some t) e1) as [se1' | ] eqn:E1; try discriminate Heval.
    destruct (sym_eval_exp ls1 gs1 (Some t) e2) as [se2' | ] eqn:E2; try discriminate Heval.
    apply IHe1 with (ot := Some t) (se1 := se1') in H2; try assumption.
    destruct H2 as [se1'' [H2_1 H2_2]].
    apply IHe2 with (ot := Some t) (se1 := se2') in H4; try assumption.
    destruct H4 as [se2'' [H4_1 H4_2]].
    simpl.
    rewrite H2_1, H4_1.
    destruct se1 as [sort1 ast1].
    destruct se1' as [sort1' ast1'].
    destruct se2' as [sort2' ast2'].
    destruct se1'' as [sort1'' ast1''].
    destruct se2'' as [sort2'' ast2''].
    assert(L1 : sort1' = sort1'').
    { apply sort_injection in H2_2. assumption. }
    assert(L2 : sort2' = sort2'').
    { apply sort_injection in H4_2. assumption. }
    subst.
    destruct sort1'', sort2''; try discriminate Heval; (
      inversion Heval; subst;
      eexists;
      split; try reflexivity;
      apply equiv_smt_expr_binop; assumption
    ).
  }
  {
    destruct (sym_eval_exp ls1 gs1 (Some (TYPE_I w)) e1) as [se1' | ] eqn:E1; try discriminate Heval.
    destruct (sym_eval_exp ls1 gs1 (Some (TYPE_I w)) (EXP_Integer n)) as [se2' | ] eqn:E2; try discriminate Heval.
    apply IHe1 with (ot := Some (TYPE_I w)) (se1 := se1') in H4; try assumption.
    destruct H4 as [se1'' [H4_1 H4_2]].
    assert(L : is_supported_exp (EXP_Integer n)).
    { apply IS_EXP_Integer. }
    apply IHe2 with (ot := Some (TYPE_I w)) (se1 := se2') in L; try assumption.
    destruct L as [se2'' [L_1 L_2]].
    simpl in L_1.
    simpl.
    rewrite H4_1, L_1.
    destruct se1 as [sort1 ast1].
    destruct se1' as [sort1' ast1'].
    destruct se2' as [sort2' ast2'].
    destruct se1'' as [sort1'' ast1''].
    destruct se2'' as [sort2'' ast2''].
    assert(L1 : sort1' = sort1'').
    { apply sort_injection in H4_2. assumption. }
    assert(L2 : sort2' = sort2'').
    { apply sort_injection in L_2. assumption. }
    subst.
    destruct sort1'', sort2''; try discriminate Heval;
    (
      inversion H2; subst;
      inversion Heval; subst;
      eexists;
      split; try reflexivity;
      apply equiv_smt_expr_binop; assumption
    ).
  }
  {
    destruct (sym_eval_exp ls1 gs1 (Some (TYPE_I w)) e1) as [se1' | ] eqn:E1; try discriminate Heval.
    destruct (sym_eval_exp ls1 gs1 (Some (TYPE_I w)) (EXP_Integer n)) as [se2' | ] eqn:E2; try discriminate Heval.
    apply IHe1 with (ot := Some (TYPE_I w)) (se1 := se1') in H4; try assumption.
    destruct H4 as [se1'' [H4_1 H4_2]].
    assert(L : is_supported_exp (EXP_Integer n)).
    { apply IS_EXP_Integer. }
    apply IHe2 with (ot := Some (TYPE_I w)) (se1 := se2') in L; try assumption.
    destruct L as [se2'' [L_1 L_2]].
    simpl in L_1.
    simpl.
    rewrite H4_1, L_1.
    destruct se1 as [sort1 ast1].
    destruct se1' as [sort1' ast1'].
    destruct se2' as [sort2' ast2'].
    destruct se1'' as [sort1'' ast1''].
    destruct se2'' as [sort2'' ast2''].
    assert(L1 : sort1' = sort1'').
    { apply sort_injection in H4_2. assumption. }
    assert(L2 : sort2' = sort2'').
    { apply sort_injection in L_2. assumption. }
    subst.
    destruct sort1'', sort2''; try discriminate Heval;
    (
      inversion H3; subst;
      inversion Heval; subst;
      eexists;
      split; try reflexivity;
      apply equiv_smt_expr_binop; assumption
    ).
  }
  {
    destruct (sym_eval_exp ls1 gs1 (Some t) e1) as [se1' | ] eqn:E1; try discriminate Heval.
    destruct (sym_eval_exp ls1 gs1 (Some t) e2) as [se2' | ] eqn:E2; try discriminate Heval.
    apply IHe1 with (ot := Some t) (se1 := se1') in H1; try assumption.
    destruct H1 as [se1'' [H1_1 H1_2]].
    apply IHe2 with (ot := Some t) (se1 := se2') in H4; try assumption.
    destruct H4 as [se2'' [H4_1 H4_2]].
    simpl.
    rewrite H1_1, H4_1.
    destruct se1 as [sort1 ast1].
    destruct se1' as [sort1' ast1'].
    destruct se2' as [sort2' ast2'].
    destruct se1'' as [sort1'' ast1''].
    destruct se2'' as [sort2'' ast2''].
    assert(L1 : sort1' = sort1'').
    { apply sort_injection in H1_2. assumption. }
    assert(L2 : sort2' = sort2'').
    { apply sort_injection in H4_2. assumption. }
    subst.
    destruct sort1'', sort2''; try discriminate Heval; (
      inversion Heval; subst;
      eexists;
      split; try reflexivity;
      apply equiv_smt_expr_cmpop; assumption
    ).
  }
  {
    destruct (sym_eval_exp ls1 gs1 (Some t1) e) as [se | ] eqn:E; try discriminate Heval.
    apply IHe with (ot := Some t1) (se1 := se) in H4; try assumption.
    destruct H4 as [se' [H4_1 H4_2]].
    simpl.
    rewrite H4_1.
    destruct se as [sort ast].
    destruct se' as [sort' ast'].
    assert(L1 : sort = sort').
    { apply sort_injection in H4_2. assumption. }
    subst.
    destruct conv; try discriminate Heval.
    {
      destruct t1; try discriminate Heval.
      destruct t2; try discriminate Heval.
      rename w into w1, w0 into w2.
      repeat (destruct w1; try discriminate Heval);
      (
        destruct sort'; try discriminate Heval;
        (
          repeat (destruct w2; try discriminate Heval);
          (
            inversion Heval; subst;
            eexists;
            split;
            [ reflexivity | apply equiv_smt_expr_extract; assumption ]
          )
        )
      ).
    }
    {
      destruct t1; try discriminate Heval.
      destruct t2; try discriminate Heval.
      rename w into w1, w0 into w2.
      repeat (destruct w1; try discriminate Heval);
      (
        destruct sort'; try discriminate Heval;
        (
          repeat (destruct w2; try discriminate Heval);
          (
            inversion Heval; subst;
            eexists;
            split;
            [ reflexivity | apply equiv_smt_expr_zext; assumption ]
          )
        )
      ).
    }
    {
      destruct t1; try discriminate Heval.
      destruct t2; try discriminate Heval.
      rename w into w1, w0 into w2.
      repeat (destruct w1; try discriminate Heval);
      (
        destruct sort'; try discriminate Heval;
        (
          repeat (destruct w2; try discriminate Heval);
          (
            inversion Heval; subst;
            eexists;
            split;
            [ reflexivity | apply equiv_smt_expr_sext; assumption ]
          )
        )
      ).
    }
    {
      destruct t1, t2; try discriminate Heval.
      rename w into w1, w0 into w2.
      simpl in Heval.
      simpl.
      destruct (w1 =? w2)%positive.
      {
        inversion Heval; subst.
        eexists.
        split.
        { reflexivity. }
        { assumption. }
      }
      { discriminate Heval. }
    }
  }
Qed.

Lemma equiv_sym_eval_phi_args : forall ls1 gs1 ls2 gs2 t args pbid se1,
  (forall bid e, In (bid, e) args -> is_supported_exp e) ->
  equiv_smt_store ls1 ls2 ->
  equiv_smt_store gs1 gs2 ->
  sym_eval_phi_args ls1 gs1 t args pbid = Some se1 ->
  (exists se2, sym_eval_phi_args ls2 gs2 t args pbid = Some se2 /\ equiv_smt_expr se1 se2).
Proof.
  intros ls1 gs1 ls2 gs2 t args pbid se1 His Heq1 Heq2 Heval.
  induction args as [ | arg args_tail].
  { discriminate Heval. }
  {
    simpl in *.
    destruct arg as [bid e].
    destruct (raw_id_eqb bid pbid) eqn:E.
    {
      rewrite raw_id_eqb_eq in E.
      apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in Heval; try assumption.
      apply (His bid e).
      left.
      reflexivity.
    }
    {
      apply IHargs_tail; try assumption.
      intros bid' e' Hin.
      apply (His bid' e').
      right.
      assumption.
    }
  }
Qed.

Lemma equiv_fill_smt_store : forall ls1 gs1 ls2 gs2 l ls1',
  equiv_smt_store ls1 ls2 ->
  equiv_smt_store gs1 gs2 ->
  (forall x arg, In (x, arg) l -> is_supported_function_arg arg) ->
  fill_smt_store ls1 gs1 l = Some ls1' ->
  exists ls2',
    fill_smt_store ls2 gs2 l = Some ls2' /\ equiv_smt_store ls1' ls2'.
Proof.
  intros ls1 gs1 ls2 gs2 l ls1' Heq1 Heq2 His Hf.
  generalize dependent ls1'.
  induction l as [ | (x, arg) tail]; intros ls1' Hf.
  {
    simpl in Hf.
    inversion Hf; subst.
    exists empty_smt_store.
    split.
    { reflexivity. }
    { apply equiv_empty_smt_store. }
  }
  {
    simpl in Hf.
    destruct arg, t.
    destruct (sym_eval_exp ls1 gs1 (Some t) e) as [se1 | ] eqn:E1.
    {
      destruct (fill_smt_store ls1 gs1 tail) as [ls1'' | ] eqn:E2.
      {
        apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in E1; try assumption.
        {
          destruct E1 as [se2 [E1_1 E1_2]].
          assert(L :
            exists ls2' : smt_store,
               fill_smt_store ls2 gs2 tail = Some ls2' /\ equiv_smt_store ls1'' ls2'
          ).
          {
            apply IHtail; try reflexivity.
            intros x' arg' Hin.
            apply (His x' arg').
            apply in_cons.
            assumption.
          }
          destruct L as [ls2'' [L_1 L_2]].
          exists (x !-> Some se2; ls2'').
          split.
          {
            simpl.
            rewrite E1_1, L_1.
            reflexivity.
          }
          {
            inversion Hf; subst.
            apply equiv_smt_store_update; assumption.
          }
        }
        {
          assert(Larg : is_supported_function_arg ((t, e), l)).
          { apply His with (x := x). apply in_eq. }
          inversion Larg; subst.
          assumption.
        }
      }
      { discriminate Hf. }
    }
    { discriminate Hf. }
  }
Qed.

Lemma equiv_create_local_store : forall ls1 gs1 ls2 gs2 d args ls1',
  equiv_smt_store ls1 ls2 ->
  equiv_smt_store gs1 gs2 ->
  (forall arg, In arg args -> is_supported_function_arg arg) ->
  create_local_smt_store d ls1 gs1 args = Some ls1' ->
  exists ls2',
    create_local_smt_store d ls2 gs2 args = Some ls2' /\ equiv_smt_store ls1' ls2'.
Proof.
  intros ls1 gs1 ls2 gs2 d args ls1' Heq1 Heq2 His Hc.
  unfold create_local_smt_store in *.
  destruct (ListUtil.merge_lists (df_args d) args) eqn:E.
  {
    apply equiv_fill_smt_store with (ls2 := ls2) (gs2 := gs2) in Hc; try assumption.
    apply ListUtil.merge_lists_preserves_prop with (xs := (df_args d)) (ys := args);
    assumption.
  }
  { discriminate Hc. }
Qed.

Inductive equiv_sym_frame : sym_frame -> sym_frame -> Prop :=
  | EquivSymFrame : forall s1 s2 ic pbid v,
      equiv_smt_store s1 s2 ->
      equiv_sym_frame (Sym_Frame s1 ic pbid v) (Sym_Frame s2 ic pbid v)
.

Inductive equiv_sym_stack : list sym_frame -> list sym_frame -> Prop :=
  | EquivSymStack_Empty :
      equiv_sym_stack [] []
  | EquivSymStack_NonEmpty : forall f1 stk1 f2 stk2,
      equiv_sym_stack stk1 stk2 ->
      equiv_sym_frame f1 f2 ->
      equiv_sym_stack (f1 :: stk1) (f2 :: stk2)
.

Lemma equiv_sym_stack_refl : forall stk,
  equiv_sym_stack stk stk.
Proof.
  intros stk.
  induction stk as [ | f stk'].
  { apply EquivSymStack_Empty. }
  {
    apply EquivSymStack_NonEmpty.
    { assumption. }
    {
      destruct f.
      apply EquivSymFrame.
      apply equiv_smt_store_refl.
    }
  }
Qed.

Lemma equiv_sym_stack_symmetry : forall stk1 stk2,
  equiv_sym_stack stk1 stk2 -> equiv_sym_stack stk2 stk1.
Proof.
  intros stk1 stk2 Heq.
  induction Heq.
  { apply EquivSymStack_Empty. }
  {
    apply EquivSymStack_NonEmpty.
    { assumption. }
    {
      inversion H; subst.
      apply EquivSymFrame.
      apply equiv_smt_store_symmetry.
      assumption.
    }
  }
Qed.

Lemma equiv_sym_stack_transivity : forall stk1 stk2 stk3,
  equiv_sym_stack stk1 stk2 -> equiv_sym_stack stk2 stk3 -> equiv_sym_stack stk1 stk3.
Proof.
  intros stk1 stk2 stk3 Heq1 Heq2.
  generalize dependent stk3.
  induction Heq1; intros stk3 Heq2.
  { assumption. }
  {
    inversion Heq2; subst.
    rename stk4 into stk3.
    apply EquivSymStack_NonEmpty.
    {
      apply IHHeq1.
      assumption.
    }
    {
      inversion H; subst.
      inversion Heq2; subst.
      inversion H8; subst.
      apply EquivSymFrame.
      apply equiv_smt_store_transitivity with (s2 := s2); assumption.
    }
  }
Qed.

Inductive equiv_sym_state : sym_state -> sym_state -> Prop :=
  | EquivSymState : forall ic c cs pbid ls1 stk1 gs1 pc1 ls2 stk2 gs2 pc2 syms mdl,
      equiv_smt_store ls1 ls2 ->
      equiv_sym_stack stk1 stk2 ->
      equiv_smt_store gs1 gs2 ->
      equiv_smt_expr (Expr Sort_BV1 pc1) (Expr Sort_BV1 pc2) ->
      equiv_sym_state
        (mk_sym_state
          ic
          c
          cs
          pbid
          ls1
          stk1
          gs1
          syms
          pc1
          mdl
        )
        (mk_sym_state
          ic
          c
          cs
          pbid
          ls2
          stk2
          gs2
          syms
          pc2
          mdl
        )
.

Lemma equiv_sym_state_refl : forall s,
  equiv_sym_state s s.
Proof.
  intros s.
  destruct s as [ic c cs pbid ls stk gs syms pc mdl].
  apply EquivSymState.
  { apply equiv_smt_store_refl. }
  { apply equiv_sym_stack_refl. }
  { apply equiv_smt_store_refl. }
  { apply equiv_smt_expr_refl. }
Qed.

Lemma equiv_sym_state_symmetry : forall s1 s2,
  equiv_sym_state s1 s2 -> equiv_sym_state s2 s1.
Proof.
  intros s1 s2 Heq.
  inversion Heq; subst.
  apply EquivSymState.
  { apply equiv_smt_store_symmetry. assumption. }
  { apply equiv_sym_stack_symmetry. assumption. }
  { apply equiv_smt_store_symmetry. assumption. }
  { apply equiv_smt_expr_symmetry. assumption. }
Qed.

Lemma equiv_sym_state_transitivity : forall s1 s2 s3,
  equiv_sym_state s1 s2 -> equiv_sym_state s2 s3 -> equiv_sym_state s1 s3.
Proof.
  intros s1 s2 s3 Heq1 Heq2.
  inversion Heq1; subst.
  inversion Heq2; subst.
  apply EquivSymState.
  { apply equiv_smt_store_transitivity with (s2 := ls2); assumption. }
  { apply equiv_sym_stack_transivity with (stk2 := stk2); assumption. }
  { apply equiv_smt_store_transitivity with (s2 := gs2); assumption. }
  {
    apply equiv_smt_expr_transitivity with (e2 := (Expr Sort_BV1 pc2));
    assumption.
  }
Qed.

Lemma error_equiv_sym_state : forall s1 s2,
  equiv_sym_state s1 s2 -> ~ error_sym_state s1 -> ~ error_sym_state s2.
Proof.
  intros s1 s2 Heq Hes1.
  inversion Heq; subst.
  intros Hes2.
  apply Hes1.
  inversion Hes2; subst.
  { apply ESS_Assert with (d := d); assumption. }
  { apply ESS_Unreachable. }
Qed.

Inductive safe_et_opt : execution_tree -> Prop :=
  | Safe_Leaf_RetVoid: forall ic cid pbid ls gs syms pc mdl,
      safe_et_opt
        (t_leaf
          (mk_sym_state
            ic
            (CMD_Term cid TERM_RetVoid)
            []
            pbid
            ls
            []
            gs
            syms
            pc
            mdl
          )
        )
  | Safe_Leaf_Ret: forall ic cid t e pbid ls gs syms pc mdl,
      safe_et_opt
        (t_leaf
          (mk_sym_state
            ic
            (CMD_Term cid (TERM_Ret (t, e)))
            []
            pbid
            ls
            []
            gs
            syms
            pc
            mdl
          )
        )
  | Safe_Subtree: forall s l,
      ~ error_sym_state s-> (* to avoid an error state with no children *)
      (forall s',
        sym_step s s' ->
        (
          (exists t, (In t l /\ safe_et_opt t /\ equiv_sym_state s' (root t))) \/ 
          (unsat_sym_state s')
        )
      ) -> safe_et_opt (t_subtree s l)
.

Lemma safe_leaf: forall s,
  safe_et_opt (t_leaf s) -> ~ error_sym_state s.
Proof.
  intros s Hs Hess.
  inversion Hs; subst; inversion Hess.
Qed.

Lemma safe_subtree: forall s l,
  safe_et_opt (t_subtree s l) -> ~ error_sym_state s.
Proof.
  intros s l Hs Hess.
  inversion Hs; subst.
  apply H1 in Hess.
  assumption.
Qed.

Lemma safe_single_step: forall s s' l,
  safe_et_opt (t_subtree s l) ->
  sym_step s s' ->
  (
    safe_et_opt (t_leaf s') \/
    (exists so' l', equiv_sym_state s' so' /\ safe_et_opt (t_subtree so' l')) \/
    unsat_sym_state s'
  ).
Proof.
  intros s s' l Hs Hss.
  inversion Hs; subst.
  apply H2 in Hss.
  destruct Hss as [Hss | Hss].
  {
    destruct Hss as [t [Hss_1 [Hss_2 Hss_3]]].
    destruct t as [x | x l'] eqn:E.
    {
      simpl in Hss_3.
      left.
      inversion Hss_2; subst.
      {
        inversion Hss_3; subst.
        inversion H13; subst.
        apply Safe_Leaf_RetVoid.
      }
      {
        inversion Hss_3; subst.
        inversion H13; subst.
        apply Safe_Leaf_Ret.
      }
    }
    {
      simpl in Hss_3.
      right.
      left.
      exists x, l'.
      split; try assumption.
    }
  }
  { right. right. assumption. }
Qed.

Lemma equiv_sym_state_on_step: forall s1 s1' s2,
  equiv_sym_state s1 s2 ->
  is_supported_sym_state s1 ->
  sym_step s1 s1' ->
  (exists s2', sym_step s2 s2' /\ equiv_sym_state s1' s2').
Proof.
  intros s1 s1' s2 Heq His Hs1.
  inversion Hs1;
  subst; rename ls into ls1, stk into stk1, gs into gs1, pc into pc1;
  inversion Heq; subst.
  {
    rename se into se1.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    {
      destruct H as [se2 [H_1 H_2]].
      exists (mk_sym_state
        (next_inst_counter ic c)
        c
        cs
        pbid
        (v !-> Some se2; ls2)
        stk2
        gs2
        syms
        pc2
        mdl
      ).
      split.
      { apply Sym_Step_OP; assumption. }
      {
        apply EquivSymState; try assumption.
        apply equiv_smt_store_update; assumption.
      }
    }
    {
      inversion His; subst.
      inversion H3; subst.
      assumption.
    }
  }
  {
    rename se into se1.
    apply equiv_sym_eval_phi_args with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    {
      destruct H as [se2 [H_1 H_2]].
      exists (mk_sym_state
        (next_inst_counter ic c)
        c
        cs
        (Some pbid)
        (v !-> Some se2; ls2)
        stk2
        gs2
        syms
        pc2
        mdl
      ).
      split.
      { apply Sym_Step_Phi; assumption. }
      {
        apply EquivSymState; try assumption.
        apply equiv_smt_store_update; assumption.
      }
    }
    {
      inversion His; subst.
      inversion H3; subst.
      assumption.
    }
  }
  {
    exists (mk_sym_state
      (mk_inst_counter (ic_fid ic) tbid (get_cmd_id c))
      c
      cs
      (Some (ic_bid ic))
      ls2
      stk2
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_UnconditionalBr with (d := d) (b := b); assumption. }
    { apply EquivSymState; try assumption. }
  }
  {
    rename cond into ast1.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    {
      destruct H as [se2 [H_1 H_2]].
      destruct se2 as [sort2 ast2].
      inversion H_2; subst.
      exists (mk_sym_state
        (mk_inst_counter (ic_fid ic) bid1 (get_cmd_id c))
        c
        cs
        (Some (ic_bid ic))
        ls2
        stk2
        gs2
        syms
        (AST_BinOp Sort_BV1 SMT_And pc2 ast2)
        mdl
      ).
      split.
      { apply Sym_Step_Br_True with (d := d) (b := b); assumption. }
      {
        apply EquivSymState; try assumption.
        apply equiv_smt_expr_binop; assumption.
      }
    }
    {
      inversion His; subst.
      inversion H6; subst.
      assumption.
    }
  }
  {
    rename cond into ast1.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    {
      destruct H as [se2 [H_1 H_2]].
      destruct se2 as [sort2 ast2].
      inversion H_2; subst.
      exists (mk_sym_state
        (mk_inst_counter (ic_fid ic) bid2 (get_cmd_id c))
        c
        cs
        (Some (ic_bid ic))
        ls2
        stk2
        gs2
        syms
        (AST_BinOp Sort_BV1 SMT_And pc2 (AST_Not Sort_BV1 ast2))
        mdl
      ).
      split.
      { apply Sym_Step_Br_False with (d := d) (b := b); assumption. }
      {
        apply EquivSymState; try assumption.
        apply equiv_smt_expr_binop; try assumption.
        apply equiv_smt_expr_not.
        assumption.
      }
    }
    {
      inversion His; subst.
      inversion H6; subst.
      assumption.
    }
  }
  {
    rename ls' into ls1'.
    assert(L :
      exists ls2',
        create_local_smt_store d ls2 gs2 args = Some ls2' /\ equiv_smt_store ls1' ls2'
    ).
    {
      apply equiv_create_local_store with (ls1 := ls1) (gs1 := gs1); try assumption.
      inversion His; subst.
      inversion H7; subst.
      assumption.
    }
    destruct L as [ls2' [L_1 L_2]].
    exists (mk_sym_state
      (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
      c'
      cs'
      None
      ls2'
      ((Sym_Frame ls2 (next_inst_counter ic c) pbid None) :: stk2)
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_VoidCall; assumption. }
    {
      apply EquivSymState; try assumption.
      apply EquivSymStack_NonEmpty; try assumption.
      apply EquivSymFrame.
      assumption.
    }
  }
  {
    rename ls' into ls1'.
    assert(L :
      exists ls2',
        create_local_smt_store d ls2 gs2 args = Some ls2' /\ equiv_smt_store ls1' ls2'
    ).
    {
      apply equiv_create_local_store with (ls1 := ls1) (gs1 := gs1); try assumption.
      inversion His; subst.
      inversion H7; subst.
      assumption.
    }
    destruct L as [ls2' [L_1 L_2]].
    exists (mk_sym_state
      (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
      c'
      cs'
      None
      ls2'
      ((Sym_Frame ls2 (next_inst_counter ic c) pbid (Some v)) :: stk2)
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_Call; assumption. }
    {
      apply EquivSymState; try assumption.
      apply EquivSymStack_NonEmpty; try assumption.
      apply EquivSymFrame.
      assumption.
    }
  }
  {
    rename ls' into ls1'.
    inversion H13; subst.
    rename stk3 into stk2.
    inversion H5; subst.
    rename s2 into ls2'.
    exists (mk_sym_state
      ic'
      c'
      cs'
      pbid'
      ls2'
      stk2
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_RetVoid with (d := d); assumption. }
    { apply EquivSymState; assumption. }
  }
  {
    rename se into se1.
    rename ls' into ls1'.
    inversion H14; subst.
    rename stk3 into stk2.
    inversion H6; subst.
    rename s2 into ls2'.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    {
      destruct H as [se2 [H_1 H_2]].
      exists (mk_sym_state
        ic'
        c'
        cs'
        pbid'
        (v !-> Some se2; ls2')
        stk2
        gs2
        syms
        pc2
        mdl
      ).
      split.
      { apply Sym_Step_Ret with (d := d); assumption. }
      {
        apply EquivSymState; try assumption.
        apply equiv_smt_store_update; assumption.
      }
    }
    {
      inversion His; subst.
      inversion H7; subst.
      assumption.
    }
  }
  {
    rename cond into ast1.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H2; try assumption.
    {
      destruct H2 as [se2 [H2_1 H2_2]].
      destruct se2 as [sort2 ast2].
      inversion H2_2; subst.
      exists (mk_sym_state
        (next_inst_counter ic c)
        c
        cs
        pbid
        ls2
        stk2
        gs2
        syms
        (AST_BinOp Sort_BV1 SMT_And pc2 ast2)
        mdl
      ).
      split.
      { apply Sym_Step_Assume with (d := d); assumption. }
      {
        apply EquivSymState; try assumption.
        apply equiv_smt_expr_binop; assumption.
      }
    }
    {
      inversion His; subst.
      inversion H6; subst.
      assert(Larg : is_supported_function_arg (TYPE_I BinNums.xH, e, attrs)).
      { apply H4. apply in_eq. }
      inversion Larg; subst.
      assumption.
    }
  }
  {
    exists (mk_sym_state
      (next_inst_counter ic c)
      c
      cs
      pbid
      (v !-> Some (Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name syms))); ls2)
      stk2
      gs2
      (extend_names syms)
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_MakeSymbolicInt32 with (d := d); assumption. }
    {
      apply EquivSymState; try assumption.
      apply equiv_smt_store_update; try assumption.
      apply equiv_smt_expr_refl.
    }
  }
Qed.

Lemma safe_subtree_equiv: forall s1 s2 l,
  equiv_sym_state s1 s2 ->
  is_supported_sym_state s1 ->
  is_supported_sym_state s2 ->
  safe_et_opt (t_subtree s1 l) ->
  safe_et_opt (t_subtree s2 l).
Proof.
  intros s1 s2 l Heq His1 His2 Hs1.
  inversion Hs1; subst.
  apply Safe_Subtree.
  { apply error_equiv_sym_state with (s1 := s1); assumption. }
  {
    intros s2' Hstep.
    apply equiv_sym_state_on_step with (s1 := s2) (s2 := s1) in Hstep.
    {
      destruct Hstep as [s1' [Hstep_1 Hstep_2]].
      specialize (H2 s1').
      apply H2 in Hstep_1.
      destruct Hstep_1 as [Hstep_1 | Hstep_1].
      {
        destruct Hstep_1 as [t [Hstep_1_1 [Hstep_1_2 Hstep_1_3]]].
        left.
        exists t.
        split.
        { assumption. }
        {
          split.
          { assumption. }
          { apply equiv_sym_state_transitivity with (s2 := s1'); assumption. }
        }
      }
      {
        right.
        inversion Hstep_2; subst.
        inversion Hstep_1; subst.
        apply Unsat_State.
        apply equiv_smt_expr_unsat with (ast1 := pc2) (ast2 := pc1).
        { apply equiv_smt_expr_symmetry. assumption. }
        { assumption. }
      }
    }
    { apply equiv_sym_state_symmetry. assumption. }
    { assumption. }
  }
Qed.

Lemma is_supported_sym_state_equiv : forall s1 s2,
  equiv_sym_state s1 s2 ->
  is_supported_sym_state s1 ->
  is_supported_sym_state s2.
Proof.
  intros s1 s2 Heq His.
  inversion Heq; subst.
  inversion His; subst.
  apply IS_SymState; assumption.
Qed.

Lemma safe_multi_step: forall s s' l,
  is_supported_sym_state s ->
  safe_et_opt (t_subtree s l) ->
  multi_sym_step s s' ->
  (
    safe_et_opt (t_leaf s') \/
    (exists so' l', equiv_sym_state s' so' /\ safe_et_opt (t_subtree so' l')) \/
    unsat_sym_state s'
  ).
Proof.
  intros s s' l His Hs Hss.
  induction Hss as [s s' | s s' s''].
  { apply safe_single_step with (s := s) (l := l); assumption. }
  {
    apply IHHss in Hs.
    destruct Hs as [Hs | [Hs | Hs]].
    { inversion Hs; subst; inversion H. }
    {
      destruct Hs as [so' [l' [Hs_1 Hs_2]]].
      apply safe_single_step with (s := s') (l := l').
      {
        apply safe_subtree_equiv with (s1 := so').
        { apply equiv_sym_state_symmetry. assumption. }
        {
          apply is_supported_sym_state_equiv with (s1 := s'); try assumption.
          apply is_supported_multi_sym_step with (s := s); assumption.
        }
        { apply is_supported_multi_sym_step with (s := s); assumption.  }
        { assumption. }
      }
      { assumption. }
    }
    {
      right.
      right.
      apply pc_unsat_lemma with (s := s'); assumption.
    }
    { assumption. }
  }
Qed.

Theorem completeness_via_et: forall mdl fid init_s l,
  is_supported_module mdl ->
  (init_sym_state mdl fid) = Some init_s ->
  safe_et_opt (t_subtree init_s l) -> 
  is_safe_program mdl fid.
Proof.
  intros mdl fid init_s l Hism Hinit Hse.
  unfold is_safe_program.
  assert(L1: exists init_c, init_state mdl fid = Some init_c).
  { apply (init_state_correspondence mdl fid). exists init_s. assumption. }
  destruct L1 as [init_c L1].
  exists init_c.
  split.
  { assumption. }
  {
    intros c Hms.
    assert(L2 :
      (exists init_s s,
        (init_sym_state mdl fid) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c)
    ).
    { apply completeness with (init_c :=  init_c); assumption. }
    destruct L2 as [init_s' [s [L2_1 [L2_2 L2_3]]]].
    rewrite L2_1 in Hinit.
    inversion Hinit; subst.
    assert(L3 :
      safe_et_opt (t_leaf s) \/
      (exists so l', equiv_sym_state s so /\ safe_et_opt (t_subtree so l')) \/
      unsat_sym_state s
    ).
    {
      apply (safe_multi_step init_s s l); try assumption.
      { apply is_supported_init_sym_state with (mdl := mdl) (fid := fid); assumption. }
    }
    destruct L3 as [L3 | [L3 | L3]].
    {
      assert(L4: ~ error_sym_state s).
      { apply safe_leaf. assumption. }
      intros Hes.
      apply error_correspondence in L2_3.
      apply L2_3 in Hes.
      apply L4.
      assumption.
    }
    {
      destruct L3 as [so [l' [L_1 L_2]]].
      assert(L4: ~ error_sym_state s).
      {
        apply error_equiv_sym_state with (s1 := so) (s2 := s).
        { apply equiv_sym_state_symmetry. assumption. }
        { apply safe_subtree with (l := l'). assumption. }
      }
      intros Hes.
      apply error_correspondence in L2_3.
      apply L2_3 in Hes.
      apply L4.
      assumption.
    }
    {
      inversion L2_3; subst.
      destruct H as [m H].
      inversion H; subst.
      inversion L3; subst.
      unfold unsat in H5.
      destruct H5.
      unfold sat.
      exists m.
      unfold sat_via.
      assumption.
    }
  }
Qed.
