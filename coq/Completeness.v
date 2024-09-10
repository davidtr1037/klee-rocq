From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import ChoiceAxiom.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import TypedExpr.
From SE.SMT Require Import TypedModel.

(* TODO: fix namespace issues *)
From SE.Utils Require Import IDMap.
From SE.Utils Require StringMap.
From SE.Utils Require ListUtil.

(* TODO: rename correspondence to over_approx? *)
Lemma eval_exp_correspondence : forall c_ls s_ls c_gs s_gs ot e m,
  is_supported_exp e ->
  over_approx_store_via s_ls c_ls m ->
  over_approx_store_via s_gs c_gs m ->
  equiv_via_model (eval_exp c_ls c_gs ot e) (sym_eval_exp s_ls s_gs ot e) m.
Proof.
Admitted.
(*
  intros c_ls s_ls c_gs s_gs ot e m His Hls Hgs.
  generalize dependent ot.
  induction e; intros ot; simpl; try (inversion His; subst).
  {
    destruct id.
    {
      unfold lookup_ident, sym_lookup_ident.
      inversion Hgs; subst.
      apply H.
    }
    {
      unfold lookup_ident, sym_lookup_ident.
      inversion Hls; subst.
      apply H.
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
    apply IHe1 with (ot := (Some t)) in H2.
    apply IHe2 with (ot := (Some t)) in H4.
    inversion H5; subst.
    destruct (eval_exp c_ls c_gs (Some t) e1) as [dv1 | ] eqn:E1.
    {
      destruct (eval_exp c_ls c_gs (Some t) e2) as [dv2 | ] eqn:E2.
      {
        inversion H2; subst.
        inversion H4; subst.
        rename se into se1, di into di1, se0 into se2, di0 into di2.
        destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2]; try (
          simpl;
          apply EVM_NoneViaModel;
          simpl;
          rewrite H1, H6;
          simpl;
          reflexivity
        ); (
          simpl;
          apply EVM_Some;
          simpl;
          rewrite H1, H6;
          simpl;
          reflexivity
        ).
      }
      {
        inversion H2; subst.
        inversion H4; subst.
        { apply EVM_None. }
        {
          apply EVM_NoneViaModel.
          simpl.
          rewrite H1, H3.
          reflexivity.
        }
      }
    }
    {
      destruct (eval_exp c_ls c_gs (Some t) e2) as [dv2 | ] eqn:E2.
      {
        inversion H2; subst.
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
        inversion H2; subst.
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
          apply EVM_NoneViaModel; (
            destruct op;
            (
              unfold sym_eval_icmp;
              simpl;
              rewrite H2, H5;
              reflexivity
            )
          )
        ); (
          simpl;
          unfold eval_icmp_generic, sym_eval_icmp;
          destruct (eval_cmp_result op n1 n2) eqn:E; (
            destruct op; (
              apply EVM_Some;
              simpl;
              rewrite H2, H5;
              unfold smt_eval_cmpop;
              simpl in *;
              rewrite E;
              reflexivity
            )
          )
        ).
      }
      {
        inversion H1; subst.
        rename se into se1, di into di1.
        inversion H4; subst.
        { apply EVM_None. }
        {
          apply EVM_NoneViaModel.
          unfold sym_eval_icmp.
          destruct op;
          (simpl; rewrite H2, H3; reflexivity).
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
          unfold sym_eval_icmp.
          destruct op;
          (simpl; rewrite H0; reflexivity).
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
            unfold sym_eval_icmp.
            destruct op;
            (simpl; rewrite H0; reflexivity).
          }
        }
      }
    }
  }
Qed.
*)

Lemma empty_store_correspondence : forall m,
  over_approx_store_via empty_smt_store empty_dv_store m.
Proof.
  intros m.
  apply OA_Store.
  intros x.
  unfold empty_dv_store, empty_smt_store.
  rewrite apply_empty_map, apply_empty_map.
  apply EVM_None.
Qed.

Lemma store_update_correspondence : forall dv se m v c_s s_s,
  equiv_via_model (Some dv) (Some se) m ->
  over_approx_store_via s_s c_s m ->
  over_approx_store_via (v !-> Some se; s_s) (v !-> Some dv; c_s) m.
Proof.
  intros dv se m v c_s s_s H1 H2.
  apply OA_Store.
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
    inversion H2; subst.
    apply H.
  }
Qed.

Lemma eval_phi_args_correspondence : forall c_ls s_ls c_gs s_gs t args pbid m,
  (forall bid e, In (bid, e) args -> is_supported_exp e) ->
  over_approx_store_via s_ls c_ls m ->
  over_approx_store_via s_gs c_gs m ->
  equiv_via_model
    (eval_phi_args c_ls c_gs t args pbid)
    (sym_eval_phi_args s_ls s_gs t args pbid)
    m.
Proof.
  intros c_ls s_ls c_gs s_gs t args pbid m His Hoal Hoag.
  induction args as [ | arg args_tail].
  {
    simpl.
    apply EVM_None.
  }
  {
    simpl.
    destruct arg as [bid e].
    destruct (raw_id_eqb bid pbid) eqn:E.
    {
      rewrite raw_id_eqb_eq in E.
      apply eval_exp_correspondence; try assumption.
      apply (His bid).
      apply in_eq.
    }
    {
      apply IHargs_tail.
      intros bid' e' Hin.
      apply (His bid').
      apply in_cons.
      assumption.
    }
  }
Qed.

Lemma fill_store_correspondence : forall c_ls s_ls c_gs s_gs m l c_ls',
  over_approx_store_via s_ls c_ls m ->
  over_approx_store_via s_gs c_gs m ->
  (forall x arg, In (x, arg) l -> is_supported_function_arg arg) ->
  fill_store c_ls c_gs l = Some c_ls' ->
  exists s_ls',
    fill_smt_store s_ls s_gs l = Some s_ls' /\ over_approx_store_via s_ls' c_ls' m.
Proof.
  intros c_ls s_ls c_gs s_gs m l c_ls' Hoac Hoag His Hc.
  generalize dependent c_ls'.
  induction l as [ | (x, arg) tail].
  {
    intros c_ls' Hc.
    exists empty_smt_store.
    split.
    { reflexivity. }
    {
      simpl in Hc.
      inversion Hc; subst.
      apply empty_store_correspondence.
    }
  }
  {
    intros c_ls' Hc.
    simpl in Hc.
    destruct arg as [y attrs]. destruct y.
    assert(L :
      equiv_via_model
        (eval_exp c_ls c_gs (Some t) e)
        (sym_eval_exp s_ls s_gs (Some t) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      specialize (His x ((t, e), attrs)).
      assert(Larg : is_supported_function_arg ((t, e), attrs)).
      { apply His. apply in_eq. }
      inversion Larg; subst.
      assumption.
    }
    destruct (eval_exp c_ls c_gs (Some t) e) as [dv | ] eqn:Eeval.
    {
      destruct (fill_store c_ls c_gs tail) as [c_ls'' | ] eqn:Efc.
      {
        assert(L2 :
          forall c_ls',
            Some c_ls'' = Some c_ls' ->
            exists s_ls' : smt_store,
              fill_smt_store s_ls s_gs tail = Some s_ls' /\
              over_approx_store_via s_ls' c_ls' m
        ).
        {
          apply IHtail.
          intros x' arg' Hin.
          apply (His x' arg').
          apply in_cons.
          assumption.
        }
        specialize (L2 c_ls'').
        destruct L2 as [s_ls'' L2].
        { reflexivity. }
        {
          destruct L2 as [L2_1 L2_2].
          inversion L; subst.
          exists (x !-> Some (TypedSMTExpr sort ast); s_ls'').
          split.
          {
            simpl.
            rewrite <- H0.
            rewrite L2_1.
            reflexivity.
          }
          {
            inversion Hc; subst.
            apply store_update_correspondence; try assumption.
            apply EVM_Some.
            reflexivity.
          }
        }
      }
      { inversion Hc. }
    }
    { discriminate Hc. }
  }
Qed.

Lemma create_local_store_correspondence : forall d c_ls c_gs s_ls s_gs m args c_ls',
  over_approx_store_via s_ls c_ls m ->
  over_approx_store_via s_gs c_gs m ->
  (forall arg, In arg args -> is_supported_function_arg arg) ->
  create_local_store d c_ls c_gs args = Some c_ls' ->
  exists s_ls',
    create_local_smt_store d s_ls s_gs args = Some s_ls' /\
    over_approx_store_via s_ls' c_ls' m.
Proof.
  intros d c_ls c_gs s_ls s_gs m args c_ls' Hoal Hoag His Hc.
  unfold create_local_store in Hc.
  unfold create_local_smt_store.
  destruct (ListUtil.merge_lists (df_args d)) eqn:E.
  {
    apply fill_store_correspondence with (c_ls := c_ls) (c_gs := c_gs); try assumption.
    apply ListUtil.merge_lists_preserves_prop with (xs := (df_args d)) (ys := args);
    assumption.
  }
  { discriminate Hc. }
Qed.

(* TODO: rename *)
Lemma LX0 : forall s x se name syms,
  well_defined_smt_store s syms ->
  ~ In name syms ->
  s x = Some se ->
  ~ contains_var se name.
Proof.
  intros s x se name syms Hwd Hin Heq.
  inversion Hwd; subst.
  specialize (H x se).
  apply H in Heq.
  inversion Heq; subst.
  specialize (H0 name).
  intros Hse.
  apply H0 in Hse.
  apply Hin in Hse.
  assumption.
Qed.

Lemma over_approx_store_non_interference : forall s_s c_s m name n syms,
  over_approx_store_via s_s c_s m ->
  well_defined_smt_store s_s syms ->
  ~ In name syms ->
  over_approx_store_via
    s_s
    c_s
    (mk_smt_model (StringMap.update_map (bv_model m) name n)).
Proof.
  intros s_s c_s m name n syms Hoa Hwd Hin.
  apply OA_Store.
  intros x.
  inversion Hoa; subst.
  specialize (H x).
  inversion H; subst.
  { apply EVM_None. }
  {
    apply EVM_Some.
    rewrite <- subexpr_non_interference with (x := name) (n := n).
    { reflexivity. }
    {
      apply (LX0 s_s x (TypedSMTExpr sort ast) name syms); try assumption.
      symmetry.
      assumption.
    }
  }
Qed.

Lemma over_approx_stack_non_interference : forall s_stk c_stk m name n syms,
  over_approx_stack_via s_stk c_stk m ->
  well_defined_stack s_stk syms ->
  ~ In name syms ->
  over_approx_stack_via
    s_stk
    c_stk
    (mk_smt_model (StringMap.update_map (bv_model m) name n))
.
Proof.
  intros s_stk c_stk m name n syms Hoa Hwd Hin.
  induction Hoa.
  { apply OA_Stack_Empty. }
  {
    apply OA_Stack_NonEmpty.
    {
      inversion H; subst.
      apply OA_Frame.
      apply over_approx_store_non_interference with (syms := syms); try assumption.
      inversion Hwd; subst.
      assumption.
    }
    {
      apply IHHoa.
      inversion Hwd; subst; assumption.
    }
  }
Qed.

Lemma infer_sort : forall (sort : smt_sort) (x : smt_sort_to_int_type sort) (n : int1),
  make_dynamic_int sort x = DI_I1 n -> sort = Sort_BV1.
Proof.
  intros sort x n H.
  destruct sort; try ( simpl in H; discriminate H ).
  { reflexivity. }
Qed.

(* TODO: remove redundant exists tactics *)
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
      apply eval_exp_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H3; subst.
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
        (v !-> Some (TypedSMTExpr sort ast); s_ls)
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
        apply OAV_State; try assumption.
        apply store_update_correspondence.
        {
          rewrite H8 in H0.
          rewrite <- H0.
          apply EVM_Some.
          reflexivity.
        }
        { assumption. }
      }
    }
  }
  {
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    assert(L :
      equiv_via_model
        (eval_phi_args c_ls c_gs t args pbid)
        (sym_eval_phi_args s_ls s_gs t args pbid)
        m
    ).
    {
      apply eval_phi_args_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H3; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H8 in *. discriminate H1. }
    {
      exists (mk_sym_state
        (next_inst_counter c_ic c)
        c
        cs
        (Some pbid)
        (v !-> Some (TypedSMTExpr sort ast); s_ls)
        s_stk
        s_gs
        s_syms
        s_pc
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Phi.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        apply store_update_correspondence.
        {
          rewrite H8 in H0.
          rewrite <- H0.
          apply EVM_Some.
          reflexivity.
        }
        { assumption. }
      }
    }
  }
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
      apply OAV_State; try assumption.
    }
  }
  { (* TERM_Br True *)
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    assert(L :
      equiv_via_model
        (eval_exp c_ls c_gs (Some (TYPE_I 1)) e)
        (sym_eval_exp s_ls s_gs (Some (TYPE_I 1)) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H3; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H8 in *. discriminate H1. }
    {
      rewrite H8 in H0.
      inversion H0; subst.
      apply infer_sort in H3.
      subst.  (* TODO: why rewrite does not work? *)
      exists (mk_sym_state
        (mk_inst_counter (ic_fid c_ic) (bid1) (get_cmd_id c))
        c
        cs
        (Some (ic_bid c_ic))
        s_ls
        s_stk
        s_gs
        s_syms
        (TypedSMT_BinOp Sort_BV1 SMT_And s_pc ast)
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Br_True with (d := d) (b := b); try assumption.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        simpl.
        inversion H0; subst.
        rewrite H26, H3.
        reflexivity.
      }
    }
  }
  {
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    assert(L :
      equiv_via_model
        (eval_exp c_ls c_gs (Some (TYPE_I 1)) e)
        (sym_eval_exp s_ls s_gs (Some (TYPE_I 1)) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H3; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H8 in *. discriminate H1. }
    {
      rewrite H8 in H0.
      inversion H0; subst.
      apply infer_sort in H3.
      subst.
      exists (mk_sym_state
        (mk_inst_counter (ic_fid c_ic) (bid2) (get_cmd_id c))
        c
        cs
        (Some (ic_bid c_ic))
        s_ls
        s_stk
        s_gs
        s_syms
        (TypedSMT_BinOp Sort_BV1 SMT_And s_pc (TypedSMT_Not Sort_BV1 ast))
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Br_False with (d := d) (b := b); try assumption.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        simpl.
        inversion H0; subst.
        rewrite H26, H3.
        reflexivity.
      }
    }
  }
  {
    rename ls' into c_ls'.
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    assert(L :
      exists s_ls',
        create_local_smt_store d s_ls s_gs args = Some s_ls' /\
        over_approx_store_via s_ls' c_ls' m
    ).
    {
      apply create_local_store_correspondence with (c_ls := c_ls) (c_gs := c_gs); try assumption.
      inversion Hiss; subst.
      inversion H3; subst.
      assumption.
    }
    destruct L as [s_ls' [L_1 L_2]].
    exists (mk_sym_state
      (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'0))
      c'0
      cs'
      None
      s_ls'
      ((Sym_Frame s_ls (next_inst_counter c_ic c) c_pbid None) :: s_stk)
      s_gs
      s_syms
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_VoidCall; assumption. }
    {
      apply OA_State.
      exists m.
      apply OAV_State; try assumption.
      apply OA_Stack_NonEmpty; try assumption.
      apply OA_Frame .
      assumption.
    }
  }
  {
    rename ls' into c_ls'.
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    assert(L :
      exists s_ls',
        create_local_smt_store d s_ls s_gs args = Some s_ls' /\
        over_approx_store_via s_ls' c_ls' m
    ).
    {
      apply create_local_store_correspondence with (c_ls := c_ls) (c_gs := c_gs); try assumption.
      inversion Hiss; subst.
      inversion H3; subst.
      assumption.
    }
    destruct L as [s_ls' [L_1 L_2]].
    exists (mk_sym_state
      (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'0))
      c'0
      cs'
      None
      s_ls'
      ((Sym_Frame s_ls (next_inst_counter c_ic c) c_pbid (Some v)) :: s_stk)
      s_gs
      s_syms
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_Call; assumption. }
    {
      apply OA_State.
      exists m.
      apply OAV_State; try assumption.
      apply OA_Stack_NonEmpty; try assumption.
      apply OA_Frame.
      assumption.
    }
  }
  {
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    inversion H22; subst.
    inversion H3; subst.
    exists (mk_sym_state
      ic'
      c'0
      cs'
      pbid'
      s_s
      s_stk0
      s_gs
      s_syms
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_RetVoid with (d := d); assumption. }
    {
      apply OA_State.
      exists m.
      apply OAV_State; assumption.
    }
  }
  {
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    inversion H23; subst.
    inversion H3; subst.
    assert(L :
      equiv_via_model
        (eval_exp c_ls c_gs (Some t) e)
        (sym_eval_exp s_ls s_gs (Some t) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H4; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H8 in *. discriminate H1. }
    {
      exists (mk_sym_state
        ic'
        c'0
        cs'
        pbid'
        (v !-> Some (TypedSMTExpr sort ast); s_s)
        s_stk0
        s_gs
        s_syms
        s_pc
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Ret with (d := d); try assumption.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        apply store_update_correspondence.
        {
          rewrite H8 in H0.
          rewrite <- H0.
          apply EVM_Some.
          reflexivity.
        }
        { assumption. }
      }
    }
  }
  {
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    inversion Hwd; subst.
    destruct H1 as [H1_1 [H1_2 [H1_3 H1_4]]].
    exists (mk_sym_state
      (next_inst_counter c_ic c)
      c
      cs
      c_pbid
      (v !-> Some (TypedSMTExpr Sort_BV32 (TypedSMT_Var Sort_BV32 (fresh_name s_syms))); s_ls)
      s_stk
      s_gs
      (extend_names s_syms)
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_MakeSymbolicInt32 with (d := d); assumption. }
    {
      apply OA_State.
      exists (
        mk_smt_model
          (StringMap.update_map (bv_model m) (fresh_name s_syms) n)
      ).
      apply OAV_State.
      {
        apply store_update_correspondence.
        {
          replace (DI_I32 (repr n)) with (make_dynamic_int Sort_BV32 (Int32.repr n)).
          {
            apply EVM_Some.
            simpl.
            rewrite StringMap.update_map_eq.
            reflexivity.
          }
          { reflexivity. }
        }
        {
          apply over_approx_store_non_interference with (syms := s_syms); try assumption.
          apply fresh_name_lemma.
        }
      }
      {
        apply over_approx_stack_non_interference with (syms := s_syms); try assumption.
        apply fresh_name_lemma.
      }
      {
        apply over_approx_store_non_interference with (syms := s_syms); try assumption.
        apply fresh_name_lemma.
      }
      {
        rewrite <- H25.
        symmetry.
        apply subexpr_non_interference.
        inversion H1_4; subst.
        specialize (H0 (fresh_name s_syms)).
        intros Hse.
        apply H0 in Hse.
        apply fresh_name_lemma in Hse.
        assumption.
      }
    }
  }
  {
    inversion Hoa; subst.
    destruct H as [m H].
    inversion H; subst.
    assert(L :
      equiv_via_model
        (eval_exp c_ls c_gs (Some (TYPE_I 1)) e)
        (sym_eval_exp s_ls s_gs (Some (TYPE_I 1)) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H3; subst.
      specialize (H1 (TYPE_I 1, e, attrs)).
      assert(Larg : is_supported_function_arg (TYPE_I 1, e, attrs)).
      { apply H1. apply in_eq. }
      inversion Larg; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H11 in *. discriminate H1. }
    {
      rewrite H11 in H0.
      inversion H0; subst.
      apply infer_sort in H3.
      subst.
      exists (mk_sym_state
        (next_inst_counter c_ic c)
        c
        cs
        c_pbid
        s_ls
        s_stk
        s_gs
        s_syms
        (TypedSMT_BinOp Sort_BV1 SMT_And s_pc ast)
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Assume with (d := d); try assumption.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        simpl.
        inversion H0; subst.
        rewrite H26, H3.
        reflexivity.
      }
    }
  }
Qed.

(* TODO: rename: init_correspondence *)
Lemma initialization_correspondence : forall mdl fid,
  (exists c, (init_state mdl fid) = Some c) <-> (exists s, (init_sym_state mdl fid) = Some s).
Proof.
  intros mdl fid.
  split; intros H.
  {
    destruct H as [c H].
    unfold init_state in H.
    destruct (find_function mdl fid) as [c_d | ] eqn:Ec_d; try discriminate H.
    destruct (build_inst_counter mdl c_d) as [c_ic | ] eqn:Ec_ic; try discriminate H.
    destruct (entry_block c_d) as [c_b | ] eqn:Ec_b; try discriminate H.
    destruct (blk_cmds c_b) as [ | c_cmd c_cmds ] eqn:Ec_cs; try discriminate H.
    exists (mk_sym_state
      c_ic
      c_cmd
      c_cmds
      None
      (init_local_smt_store mdl c_d)
      []
      (init_global_smt_store mdl)
      []
      smt_ast_true
      mdl
    ).
    unfold init_sym_state.
    simpl.
    rewrite Ec_d, Ec_ic, Ec_b, Ec_cs.
    reflexivity.
  }
  {
    destruct H as [s H].
    unfold init_sym_state in H.
    destruct (find_function mdl fid) as [s_d | ] eqn:Es_d; try discriminate H.
    destruct (build_inst_counter mdl s_d) as [s_ic | ] eqn:Es_ic; try discriminate H.
    destruct (entry_block s_d) as [s_b | ] eqn:Es_b; try discriminate H.
    destruct (blk_cmds s_b) as [ | s_cmd s_cmds ] eqn:Es_cs; try discriminate H.
    exists (mk_state
      s_ic
      s_cmd
      s_cmds
      None
      (init_local_store mdl s_d)
      []
      (init_global_store mdl)
      mdl
    ).
    unfold init_state.
    simpl.
    rewrite Es_d, Es_ic, Es_b, Es_cs.
    reflexivity.
  }
Qed.

Lemma over_approx_init_states : forall mdl fid s c,
  init_sym_state mdl fid = Some s ->
  init_state mdl fid = Some c ->
  over_approx s c.
Proof.
  intros mdl fid s c Hs Hc.
  unfold init_sym_state in Hs.
  destruct (find_function mdl fid) as [s_d | ] eqn:Es_d; try discriminate Hs.
  destruct (build_inst_counter mdl s_d) as [s_ic | ] eqn:Es_ic; try discriminate Hs.
  destruct (entry_block s_d) as [s_b | ] eqn:Es_b; try discriminate Hs.
  destruct (blk_cmds s_b) as [ | s_cmd s_cmds ] eqn:Es_cs; try discriminate Hs.
  unfold init_state in Hc.
  destruct (find_function mdl fid) as [c_d | ] eqn:Ec_d; try discriminate Hc.
  destruct (build_inst_counter mdl c_d) as [c_ic | ] eqn:Ec_ic; try discriminate Hc.
  destruct (entry_block c_d) as [c_b | ] eqn:Ec_b; try discriminate Hc.
  destruct (blk_cmds c_b) as [ | c_cmd c_cmds ] eqn:Ec_cs; try discriminate Hc.
  inversion Es_d; subst.
  rewrite Ec_ic in Es_ic.
  inversion Es_ic; subst.
  rewrite Ec_b in Es_b.
  inversion Es_b; subst.
  rewrite Ec_cs in Es_cs.
  inversion Es_cs; subst.
  apply OA_State.
  exists default_model.
  inversion Hs; subst.
  inversion Hc; subst.
  apply OAV_State.
  {
    unfold init_local_smt_store, init_local_store.
    apply empty_store_correspondence.
  }
  { apply OA_Stack_Empty. }
  {
    unfold init_global_smt_store, init_global_store.
    apply empty_store_correspondence.
  }
  { reflexivity. }
Qed.

Lemma completeness :
  forall (mdl : llvm_module) (fid : function_id) (init_c c : state),
    is_supported_module mdl ->
    (init_state mdl fid) = Some init_c ->
    multi_step init_c c ->
    (exists init_s s,
      (init_sym_state mdl fid) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c).
Proof.
  intros mdl fid init_c c Hism Hinit Hms.
  (* TODO: rename *)
  assert(L1 : exists init_s, init_sym_state mdl fid = Some init_s).
  { apply (initialization_correspondence mdl fid). exists init_c. assumption. }
  destruct L1 as [init_s L1].
  exists init_s.
  induction Hms as [init_c c | init_c c c'].
  {
    (* TODO: rename *)
    assert(L2 : exists s, sym_step init_s s /\ over_approx s c).
    {
      apply completeness_single_step with (c := init_c).
      { apply (is_supported_init_state mdl fid); assumption. }
      { assumption. }
      { apply (well_defined_init_sym_state mdl fid). assumption. }
      { apply (over_approx_init_states mdl fid); assumption. }
    }
    destruct L2 as [s [L2_1 L2_2]].
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
    assert(L3 :
      exists s,
        init_sym_state mdl fid = Some init_s /\ multi_sym_step init_s s /\ over_approx s c
    ).
    { apply IHHms. assumption. }
    destruct L3 as [s [L3_1 [L3_2 L3_3]]].
    (* TODO: rename *)
    assert(L4 : exists s', sym_step s s' /\ over_approx s' c').
    {
      apply completeness_single_step with (c := c).
      {
        apply (is_supported_multi_step init_c); try assumption.
        apply (is_supported_init_state mdl fid); assumption.
      }
      { assumption. }
      {
        apply well_defined_multi_sym_step with (s := init_s).
        apply (well_defined_init_sym_state mdl fid).
        { assumption. }
        { assumption. }
      }
      { assumption. }
    }
    destruct L4 as [s' [L4_1 L4_2]].
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
