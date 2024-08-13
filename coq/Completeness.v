From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import Module.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

(* TODO: rename *)
Lemma smt_lemma_1 : forall c_ls s_ls c_gs s_gs ot e m,
  (forall (x : raw_id), equiv_via_model (c_ls x) (s_ls x) m) ->
  (forall (x : raw_id), equiv_via_model (c_gs x) (s_gs x) m) ->
  equiv_via_model (eval_exp c_ls c_gs ot e) (sym_eval_exp s_ls s_gs ot e) m.
Proof.
Admitted.

Lemma smt_lemma_2 : forall c_ls s_ls c_gs s_gs ot e m,
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
      apply smt_lemma_2; try assumption.
      inversion Hiss; subst.
      inversion H2; subst.
      assumption.
    }
    inversion L; subst.
    { simpl in H8. rewrite H8 in *. discriminate H1. }
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
          intros x.
          destruct (raw_id_eqb x v) eqn:E.
          {
            rewrite raw_id_eqb_eq in E.
            rewrite E.
            rewrite update_map_eq, update_map_eq.
            rewrite H8 in H0.
            rewrite <- H0.
            apply EVM_NoneViaModel.
            assumption.
          }
          {
            rewrite raw_id_eqb_neq in E.
            rewrite update_map_neq, update_map_neq; try (symmetry; assumption).
            apply H20_1.
          }
        }
        {
          split.
          { apply H20_2. }
          { assumption. }
        }
      }
    }
    { admit. }
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

(* TODO: add module preconditions *)
Lemma completeness :
  forall (mdl : llvm_module) (d : llvm_definition) (c : state),
    exists init_c,
      (init_state mdl d) = Some init_c ->
      multi_step init_c c ->
      (exists init_s s,
        (init_sym_state mdl d) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c).
Proof.
Admitted.
