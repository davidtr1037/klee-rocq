From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

(* TODO: rename *)
Lemma eval_correspondence : forall c_ls s_ls c_gs s_gs ot e m,
  is_supported_exp e ->
  (forall (x : raw_id), equiv_via_model (c_ls x) (s_ls x) m) ->
  (forall (x : raw_id), equiv_via_model (c_gs x) (s_gs x) m) ->
  equiv_via_model (eval_exp c_ls c_gs ot e) (sym_eval_exp s_ls s_gs ot e) m.
Proof.
  intros c_ls s_ls c_gs s_gs ot e m His Hls Hgs.
  generalize dependent ot.
  induction e; intros ot; simpl; try (inversion His; subst).
  {
    destruct id.
    {
      unfold lookup_ident, sym_lookup_ident.
      apply Hgs.
    }
    {
      unfold lookup_ident, sym_lookup_ident.
      apply Hls.
    }
  }
  {
    destruct ot.
    {
      destruct t; try (apply EVM_None).
      repeat (destruct w; try (apply EVM_None)); (apply EVM_Some; reflexivity).
    }
    { apply EVM_None. }
  }
  {
    apply IHe1 with (ot := (Some t)) in H1.
    apply IHe2 with (ot := (Some t)) in H4.
    destruct (eval_exp c_ls c_gs (Some t) e1) as [dv1 | ] eqn:E1.
    {
      destruct (eval_exp c_ls c_gs (Some t) e2) as [dv2 | ] eqn:E2.
      {
        inversion H1; subst.
        inversion H4; subst.
        rename se into se1, di into di1, se0 into se2, di0 into di2.
        destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2]; try (
          simpl;
          apply EVM_NoneViaModel;
          simpl;
          rewrite H2, H5;
          simpl;
          reflexivity
        ); (
          simpl;
          apply EVM_Some;
          simpl;
          rewrite H2, H5;
          simpl;
          reflexivity
        ).
      }
      {
        inversion H1; subst.
        inversion H4; subst.
        { apply EVM_None. }
        {
          apply EVM_NoneViaModel.
          simpl.
          rewrite H2, H3.
          reflexivity.
        }
      }
    }
    {
      destruct (eval_exp c_ls c_gs (Some t) e2) as [dv2 | ] eqn:E2.
      {
        inversion H1; subst.
        { apply EVM_None. }
        {
          inversion H4; subst.
          apply EVM_NoneViaModel.
          simpl.
          rewrite H0.
          reflexivity.
        }
      }
      {
        inversion H1; subst.
        { apply EVM_None. }
        {
          rename se into se1.
          inversion H4; subst.
          { apply EVM_None. }
          {
            rename se into se2.
            apply EVM_NoneViaModel.
            simpl.
            rewrite H0.
            reflexivity.
          }
        }
      }
    }
  }
Qed.

Lemma store_correspondence_update : forall dv se m v c_s s_s,
  equiv_via_model (Some dv) (Some se) m ->
  (forall x, equiv_via_model (c_s x) (s_s x) m) ->
  (forall x, equiv_via_model ((v !-> Some dv; c_s) x) ((v !-> Some se; s_s) x) m).
Proof.
  intros dv se m v c_s s_s H1 H2.
  intros x.
  destruct (raw_id_eqb x v) eqn:E.
  {
    rewrite raw_id_eqb_eq in E.
    rewrite E.
    rewrite update_map_eq, update_map_eq.
    assumption.
  }
  {
    rewrite raw_id_eqb_neq in E.
    rewrite update_map_neq, update_map_neq; try (symmetry; assumption).
    apply H2.
  }
Qed.

Lemma completeness_single_step :
  forall c c' s,
    is_supported_state c ->
    step c c' ->
    well_defined s ->
    over_approx s c ->
    (exists s', sym_step s s' /\ over_approx s' c').
Proof.
  intros c c' s Hiss Hs Hwd Hoa.
  destruct c as [c_ic c_c c_cs c_pbid c_ls c_stk c_gs c_mdl].
  destruct s as [s_ic s_c s_cs s_pbid s_ls s_stk s_gs s_syms s_pc s_mdl].
  inversion Hs; subst.
  {
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    assert(L :
      equiv_via_model
        (eval_exp c_ls c_gs None e)
        (sym_eval_exp s_ls s_gs None e)
        m
    ).
    {
      destruct H20 as [H20_1 [H20_2 H20_3]].
      apply eval_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H2; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H8 in *. discriminate H1. }
    {
      exists (mk_sym_state
        (next_inst_counter c_ic c)
        c
        cs
        c_pbid
        (v !-> Some se; s_ls)
        s_stk
        s_gs
        s_syms
        s_pc
        c_mdl
      ).
      split.
      {
        apply Sym_Step_OP.
        symmetry.
        simpl.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State.
        destruct H20 as [H20_1 [H20_2 H20_3]].
        split.
        {
          apply store_correspondence_update.
          {
            rewrite H8 in H0.
            rewrite <- H0.
            apply EVM_NoneViaModel.
            assumption.
          }
          { assumption. }
        }
        {
          split.
          { apply H20_2. }
          { assumption. }
        }
      }
    }
    {
      exists (mk_sym_state
        (next_inst_counter c_ic c)
        c
        cs
        c_pbid
        (v !-> Some se; s_ls)
        s_stk
        s_gs
        s_syms
        s_pc
        c_mdl
      ).
      split.
      {
        apply Sym_Step_OP.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State.
        destruct H20 as [H20_1 [H20_2 H20_3]].
        split.
        {
          apply store_correspondence_update.
          {
            rewrite H8 in H0.
            rewrite <- H0.
            apply EVM_Some.
            assumption.
          }
          { assumption. }
        }
        { split; assumption. }
      }
    }
  }
  { admit. }
  {
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    exists (mk_sym_state
      (mk_inst_counter (ic_fid c_ic) (tbid) (get_cmd_id c))
      c
      cs
      (Some (ic_bid c_ic))
      s_ls
      s_stk
      s_gs
      s_syms
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_UnconditionalBr with (d := d) (b := b); assumption. }
    {
      apply OA_State.
      exists m.
      apply OAV_State.
      destruct H22 as [H22_1 [H22_2 H22_3]].
      split.
      { assumption. }
      { split; assumption. }
    }
  }
Admitted.

(* TODO: should be iff *)
Lemma initialization_correspondence : forall mdl d,
  (exists c, (init_state mdl d) = Some c) <-> (exists s, (init_sym_state mdl d) = Some s).
Proof.
Admitted.

Lemma over_approx_init_states : forall mdl d s c,
  init_sym_state mdl d = Some s ->
  init_state mdl d = Some c ->
  over_approx s c.
Proof.
Admitted.

Lemma completeness :
  forall (mdl : llvm_module) (d : llvm_definition) (init_c c : state),
    is_supported_module mdl ->
    (init_state mdl d) = Some init_c ->
    multi_step init_c c ->
    (exists init_s s,
      (init_sym_state mdl d) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c).
Proof.
  intros mdl d init_c c Hism Hinit Hms.
  (* TODO: rename *)
  assert(L0: exists init_s, init_sym_state mdl d = Some init_s).
  { apply (initialization_correspondence mdl d). exists init_c. assumption. }
  destruct L0 as [init_s L0].
  exists init_s.
  induction Hms as [init_c c | init_c c c'].
  {
    (* TODO: rename *)
    assert(L1: exists s, sym_step init_s s /\ over_approx s c).
    {
      apply completeness_single_step with (c := init_c).
      { apply (init_state_supported mdl d); assumption. }
      { assumption. }
      { apply (well_defined_init_sym_state mdl d). assumption. }
      { apply (over_approx_init_states mdl d); assumption. }
    }
    destruct L1 as [s [L1_1 L1_2]].
    exists s.
    split.
    { assumption. }
    {
      split.
      { apply multi_base. assumption. }
      { assumption. }
    }
  }
  {
    (* TODO: rename *)
    assert(L2:
      exists s,
        init_sym_state mdl d = Some init_s /\ multi_sym_step init_s s /\ over_approx s c
    ).
    { apply IHHms. assumption. }
    destruct L2 as [s [L2_1 [L2_2 L2_3]]].
    (* TODO: rename *)
    assert(L3: exists s', sym_step s s' /\ over_approx s' c').
    {
      apply completeness_single_step with (c := c).
      {
        apply (multi_step_supported mdl init_c); try assumption.
        apply (init_state_supported mdl d); assumption.
      }
      { assumption. }
      {
        apply well_defined_multi_sym_step with (s := init_s).
        apply (well_defined_init_sym_state mdl d).
        { assumption. }
        { assumption. }
      }
      { assumption. }
    }
    destruct L3 as [s' [L3_1 L3_2]].
    exists s'.
    split.
    { assumption. }
    {
      split.
      { apply multi_trans with (y := s); assumption. }
      { assumption. }
    }
  }
Qed.
