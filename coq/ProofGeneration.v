From Coq Require Import List.
From Coq Require Import Logic.Eqdep.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import ChoiceAxiom.
From SE Require Import Completeness.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import ExecutionTreeOpt.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

From SE.Utils Require Import IDMap.
From SE.Utils Require Import Util.

Lemma in_list_0 : forall (t : execution_tree) l,
  In t (t :: l).
Proof.
  intros t l.
  apply in_eq.
Qed.

Lemma in_list_1 : forall (t1 t2 : execution_tree) l,
  In t2 (t1 :: (t2 :: l)).
Proof.
  intros t1 t2 l.
  right.
  apply in_eq.
Qed.

Lemma not_error_instr_op : forall ic cid v e cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v e))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid v e cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma not_error_phi : forall ic cid v t args cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Phi cid (Phi v t args))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid v t args cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma not_error_unconditional_br : forall ic cid bid cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_UnconditionalBr bid))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid bid cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma not_error_br : forall ic cid e bid1 bid2 cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_Br e bid1 bid2))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid e bid1 bid2 cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma not_error_call : forall ic cid v f args anns cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Call v f args anns))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid v f args anns cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma not_error_void_call : forall ic cid f args anns cs pbid ls stk gs syms pc mdl,
  f <> (TYPE_Void, assert_exp) ->
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_VoidCall f args anns))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid f args anns cs pbid ls stk gs syms pc mdl Hf.
  intros H.
  inversion H; subst.
  apply Hf.
  reflexivity.
Qed.

Lemma not_error_ret : forall ic cid e cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_Ret e))
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid e cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma not_error_ret_void : forall ic cid cs pbid ls stk gs syms pc mdl,
  ~ error_sym_state
    (mk_sym_state
      ic
      (CMD_Term cid TERM_RetVoid)
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic cid cs pbid ls stk gs syms pc mdl.
  intros H.
  inversion H.
Qed.

Lemma equiv_smt_store_via_some_injection : forall ls1 ls2 ls3,
  Some ls1 = Some ls2 ->
  equiv_smt_store ls1 ls3 ->
  equiv_smt_store ls2 ls3.
Proof.
  intros ls1 ls2 ls3 Hs Heq.
  inversion Hs; subst.
  assumption.
Qed.

Lemma equiv_smt_store_on_update : forall s v se1 se2 se3,
  Some se1 = Some se2 ->
  equiv_smt_expr se1 se3 ->
  equiv_smt_store (v !-> Some se2; s) (v !-> Some se3; s).
Proof.
  intros s v se1 se2 se3 H Heq.
  inversion H; subst.
  apply equiv_smt_store_update.
  { apply equiv_smt_store_refl. }
  { assumption. }
Qed.

Lemma equiv_smt_store_on_update_same : forall s v se1 se2,
  Some se1 = Some se2 ->
  equiv_smt_store (v !-> Some se2; s) (v !-> Some se1; s).
Proof.
  intros s v se1 se2 H.
  inversion H; subst.
  apply equiv_smt_store_refl.
Qed.

Lemma equiv_smt_store_on_optimized_update: forall m x se1 se2 se3 l,
  equiv_smt_expr se2 se3 ->
  equiv_smt_store
    (x !-> Some se2; (multi_update_map (x !-> Some se1; m) l))
    (x !-> Some se3; (multi_update_map m l)).
Proof.
  intros m x se1 se2 se3 l Heq.
  apply EquivSMTStore.
  intros y.
  destruct (raw_id_eqb x y) eqn:E.
  {
    apply raw_id_eqb_eq in E.
    rewrite E.
    rewrite update_map_eq, update_map_eq.
    right.
    exists se2, se3.
    split; try reflexivity.
    split; try reflexivity.
    assumption.
  }
  {
    apply raw_id_eqb_neq in E.
    rewrite update_map_neq, update_map_neq; try (assumption).
    assert(L: (multi_update_map (x !-> Some se1; m) l y) = (multi_update_map m l y)).
    {
      apply lemma_multi_update_map_2.
      assumption.
    }
    rewrite L.
    destruct (multi_update_map m l y) as [se | ] eqn:Ey.
    {
      right.
      exists se, se.
      split; try reflexivity.
      split; try reflexivity.
      apply equiv_smt_expr_refl.
    }
    {
      left.
      split; reflexivity.
    }
  }
Qed.

Lemma equiv_smt_expr_implied_condition: forall ast1 ast2,
  unsat (AST_BinOp Sort_BV1 SMT_And ast1 (AST_Not Sort_BV1 ast2)) ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast1 ast2))
    (Expr Sort_BV1 ast1).
Proof.
  intros ast1 ast2 Hunsat.
  apply EquivExpr.
  intros m.
  unfold unsat, sat in Hunsat.
  assert(L1 :
    (smt_eval_ast m Sort_BV1 ast1) = Int1.zero \/
    (smt_eval_ast m Sort_BV1 ast1) = Int1.one
  ).
  { apply int1_destruct. }
  destruct L1 as [L1 | L1].
  {
    simpl.
    rewrite L1.
    apply Int1.and_zero_l.
  }
  {
    unfold sat_via in Hunsat.
    simpl in *.
    assert(L2 :
      (smt_eval_ast m Sort_BV1 ast2) = Int1.zero \/
      (smt_eval_ast m Sort_BV1 ast2) = Int1.one
    ).
    { apply int1_destruct. }
    destruct L2 as [L2 | L2].
    {
      destruct Hunsat.
      exists m.
      rewrite L1, L2.
      reflexivity.
    }
    {
      rewrite L1, L2.
      reflexivity.
    }
  }
Qed.

Lemma implied_condition: forall ast1 ast2 ast3,
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast1 (AST_Not Sort_BV1 ast2)))
    (Expr Sort_BV1 ast3) ->
  unsat ast3 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast1 ast2))
    (Expr Sort_BV1 ast1).
Proof.
  intros ast1 ast2 ast3 Heq Hunsat.
  apply equiv_smt_expr_implied_condition.
  apply equiv_smt_expr_unsat with (ast1 := ast3).
  { apply equiv_smt_expr_symmetry. assumption. }
  { assumption. }
Qed.

Lemma equiv_smt_expr_not_not : forall (ast : smt_ast Sort_BV1),
  equiv_smt_expr
    (Expr Sort_BV1 ast)
    (Expr Sort_BV1 (AST_Not Sort_BV1 (AST_Not Sort_BV1 ast))).
Proof.
  intros ast.
  apply EquivExpr.
  intros m.
  simpl.
  assert(L :
    (smt_eval_ast m Sort_BV1 ast) = Int1.zero \/ (smt_eval_ast m Sort_BV1 ast) = Int1.one
  ).
  { apply int1_destruct. }
  destruct L as [L | L]; rewrite L; reflexivity.
Qed.

Lemma implied_negated_condition: forall ast1 ast2 ast3,
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast1 ast2))
    (Expr Sort_BV1 ast3) ->
  unsat ast3 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast1 (AST_Not Sort_BV1 ast2)))
    (Expr Sort_BV1 ast1).
Proof.
  intros ast1 ast2 ast3 Heq Hunsat.
  apply (implied_condition ast1 (AST_Not Sort_BV1 ast2) ast3).
  {
    apply equiv_smt_expr_transitivity with
      (e2 := (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast1 ast2))).
    {
      apply equiv_smt_expr_binop.
      { apply equiv_smt_expr_refl. }
      {
        apply equiv_smt_expr_symmetry.
        apply equiv_smt_expr_not_not.
      }
    }
    { assumption. }
  }
  { assumption. }
Qed.

Lemma injection_expr : forall (sort : smt_sort) (ast1 ast2 : smt_ast sort),
  Expr sort ast1 = Expr sort ast2 ->
  ast1 = ast2.
Proof.
  intros sort ast1 ast2 H.
  inversion H.
  apply inj_pair2.
  assumption.
Qed.

(* TODO: rename *)
Lemma equiv_smt_expr_1 : forall se se_no_opt se_opt,
  Some se_no_opt = Some se ->
  equiv_smt_expr se_no_opt se_opt ->
  equiv_smt_expr se se_opt.
Proof.
  intros se se_no_opt se_opt Heq Hequiv.
  apply injection_some in Heq.
  subst.
  assumption.
Qed.

Lemma equiv_smt_expr_via_some_injection : forall se1 se2,
  Some se1 = Some se2 ->
  equiv_smt_expr se2 se1.
Proof.
  intros se1 se2 Heq.
  apply injection_some in Heq.
  subst.
  apply equiv_smt_expr_refl.
Qed.

(* helps to avoid subst *)
Lemma equiv_pc_1 : forall ast1 ast2 ast3 ast4,
  Some (Expr Sort_BV1 ast1) = Some (Expr Sort_BV1 ast2) ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast3 ast1))
    (Expr Sort_BV1 (ast4)) ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast3 ast2))
    (Expr Sort_BV1 (ast4)).
Proof.
  intros ast1 ast2 ast3 ast4 Heq Hequiv.
  apply injection_some in Heq.
  apply injection_expr in Heq.
  subst.
  assumption.
Qed.

Lemma equiv_pc_2 : forall ast1 ast2 ast3 ast4,
  Some (Expr Sort_BV1 ast1) = Some (Expr Sort_BV1 ast2) ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast3 ast1))
    (Expr Sort_BV1 (ast4)) ->
  equiv_smt_expr
    (Expr Sort_BV1 (ast4))
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast3 ast2)).
Proof.
  intros ast1 ast2 ast3 ast4 Heq Hequiv.
  apply equiv_smt_expr_symmetry.
  apply equiv_pc_1 with (ast1 := ast1); assumption.
Qed.

Lemma inversion_instr_op : forall ic cid v e c cs pbid ls stk gs syms pc mdl s,
      sym_step
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_Op v e))
          (c :: cs)
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        s ->
      exists se,
        (sym_eval_exp ls gs None e) = Some se /\
        s = (mk_sym_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> Some se; ls)
          stk
          gs
          syms
          pc
          mdl
        ).
Proof.
  intros ic cid v e c cs pbid ls stk gs syms pc mdl s Hstep.
  inversion Hstep; subst.
  exists se.
  split; try assumption.
  reflexivity.
Qed.

Lemma equiv_sym_state_instr_op : forall ic cid v e c cs pbid ls stk gs syms pc mdl ls_opt s,
  equiv_smt_store (v !-> (sym_eval_exp ls gs None e); ls) ls_opt ->
  sym_step
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v e))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    )
    s ->
    equiv_sym_state
      s
      (mk_sym_state
        (next_inst_counter ic c)
        c
        cs
        pbid
        ls_opt
        stk
        gs
        syms
        pc
        mdl
      ).
Proof.
  intros ic cid v e c cs pbid ls stk gs syms pc mdl ls_opt s Heq Hstep.
  apply inversion_instr_op in Hstep.
  destruct Hstep as [se' [Heval' Hs]].
  subst.
  rewrite Heval' in Heq.
  apply EquivSymState.
  { assumption. }
  { apply equiv_sym_stack_refl. }
  { apply equiv_smt_store_refl. }
  { apply equiv_smt_expr_refl. }
Qed.

Lemma inversion_phi : forall ic cid v t args c cs pbid ls stk gs syms pc mdl s,
  sym_step
    (mk_sym_state
      ic
      (CMD_Phi cid (Phi v t args))
      (c :: cs)
      (Some pbid)
      ls
      stk
      gs
      syms
      pc
      mdl
    )
    s ->
    exists se,
      (sym_eval_phi_args ls gs t args pbid) = Some se /\
      s = (mk_sym_state
        (next_inst_counter ic c)
        c
        cs
        (Some pbid)
        (v !-> Some se; ls)
        stk
        gs
        syms
        pc
        mdl
      ).
Proof.
  intros ic cid v t args c cs pbid ls stk gs syms pc mdl s Hstep.
  inversion Hstep.
  exists se.
  split; try assumption.
  reflexivity.
Qed.

Lemma inversion_unconditional_br : forall ic cid tbid pbid ls stk gs syms pc mdl s,
  sym_step
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_UnconditionalBr tbid))
      []
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    )
    s ->
  exists d b c cs,
    (find_function mdl (ic_fid ic)) = Some d /\
    (fetch_block d tbid) = Some b /\
    (blk_cmds b) = c :: cs /\
    s = (mk_sym_state
        (mk_inst_counter (ic_fid ic) tbid (get_cmd_id c))
        c
        cs
        (Some (ic_bid ic))
        ls
        stk
        gs
        syms
        pc
        mdl
      ).
Proof.
  intros ic cid tbid pbid ls stk gs syms pc mdl s Hstep.
  inversion Hstep; subst.
  exists d, b, c, cs.
  split; try assumption.
  split; try assumption.
  split; try assumption.
  reflexivity.
Qed.

Lemma inversion_br : forall ic cid e bid1 bid2 pbid ls stk gs syms pc mdl s,
  sym_step
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_Br ((TYPE_I 1), e) bid1 bid2))
      []
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    )
    s ->
  exists cond d b c cs,
    (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some (Expr Sort_BV1 cond) /\
    (find_function mdl (ic_fid ic)) = Some d /\
    (
      (
        (fetch_block d bid1) = Some b /\
        (blk_cmds b) = c :: cs /\
        s = (mk_sym_state
          (mk_inst_counter (ic_fid ic) bid1 (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          syms
          (AST_BinOp Sort_BV1 SMT_And pc cond)
          mdl
        )
      ) \/
      (
        (fetch_block d bid2) = Some b /\
        (blk_cmds b) = c :: cs /\
        s = (mk_sym_state
          (mk_inst_counter (ic_fid ic) bid2 (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          syms
          (AST_BinOp Sort_BV1 SMT_And pc (AST_Not Sort_BV1 cond))
          mdl
        )
      )
    ).
Proof.
  intros ic cid e bid1 bid2 pbid ls stk gs syms pc mdl s Hstep.
  inversion Hstep; subst.
  {
    exists cond, d, b, c, cs.
    split; try assumption.
    split; try assumption.
    left.
    split; try assumption.
    split; try assumption.
    reflexivity.
  }
  {
    exists cond, d, b, c, cs.
    split; try assumption.
    split; try assumption.
    right.
    split; try assumption.
    split; try assumption.
    reflexivity.
  }
Qed.

Lemma inversion_call : forall ic cid v t f args anns c cs pbid ls stk gs syms pc mdl d s,
  (find_function_by_exp mdl f) = Some d ->
  sym_step
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Call v (t, f) args anns))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    )
    s ->
    exists b c' cs' ls',
      (dc_type (df_prototype d)) = TYPE_Function t (get_arg_types args) false /\
      (entry_block d) = Some b /\
      (blk_cmds b) = c' :: cs' /\
      (create_local_smt_store d ls gs args) = Some ls' /\
      s = (mk_sym_state
        (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
        c'
        cs'
        None
        ls'
        ((Sym_Frame ls (next_inst_counter ic c) pbid (Some v)) :: stk)
        gs
        syms
        pc
        mdl
      ).
Proof.
  intros ic cid v t f args anns c cs pbid ls stk gs syms pc mdl d s Hd Hstep.
  inversion Hstep; subst.
  exists b, c', cs', ls'.
  {
    rewrite Hd in H16.
    inversion H16; subst.
    rename d0 into d.
    split; try assumption.
    split; try assumption.
    split; try assumption.
    split; try assumption.
    reflexivity.
  }
  {
    unfold find_function_by_exp in Hd.
    simpl in Hd.
    rewrite Hd in H16.
    discriminate H16.
  }
Qed.

Lemma inversion_void_call : forall ic cid f args anns c cs pbid ls stk gs syms pc mdl d s,
  (find_function_by_exp mdl f) = Some d ->
  sym_step
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, f) args anns))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    )
    s ->
    exists b c' cs' ls',
      (dc_type (df_prototype d)) = TYPE_Function TYPE_Void (get_arg_types args) false /\
      (entry_block d) = Some b /\
      (blk_cmds b) = c' :: cs' /\
      (create_local_smt_store d ls gs args) = Some ls' /\
      s = (mk_sym_state
        (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
        c'
        cs'
        None
        ls'
        ((Sym_Frame ls (next_inst_counter ic c) pbid None) :: stk)
        gs
        syms
        pc
        mdl
      ).
Proof.
  intros ic cid f args anns c cs pbid ls stk gs syms pc mdl d s Hd Hstep.
  inversion Hstep; subst.
  exists b, c', cs', ls'.
  {
    rewrite Hd in H14.
    inversion H14; subst.
    rename d0 into d.
    split; try assumption.
    split; try assumption.
    split; try assumption.
    split; try assumption.
    reflexivity.
  }
  {
    unfold find_function_by_exp in Hd.
    simpl in Hd.
    rewrite Hd in H14.
    discriminate H14.
  }
Qed.

Lemma inversion_ret : forall ic cid t e pbid ls ls' ic' pbid' v stk gs syms pc mdl s,
  sym_step
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_Ret (t, e)))
      []
      pbid
      ls
      ((Sym_Frame ls' ic' pbid' (Some v)) :: stk)
      gs
      syms
      pc
      mdl
    )
    s ->
    exists se d c' cs',
      (sym_eval_exp ls gs (Some t) e) = Some se /\
      (find_function mdl (ic_fid ic')) = Some d /\
      (get_trailing_cmds d ic') = Some (c' :: cs') /\
      s = (mk_sym_state
        ic'
        c'
        cs'
        pbid'
        (v !-> Some se; ls')
        stk
        gs
        syms
        pc
        mdl
      ).
Proof.
  intros ic cid t e pbid ls ls' ic' pbid' v stk gs syms pc mdl s Hstep.
  inversion Hstep; subst.
  exists se, d, c', cs'.
  split; try assumption.
  split; try assumption.
  split; try assumption.
  reflexivity.
Qed.

Lemma inversion_ret_void : forall ic cid pbid ls ls' ic' pbid' stk gs syms pc mdl s,
  sym_step
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_RetVoid))
      []
      pbid
      ls
      ((Sym_Frame ls' ic' pbid' None) :: stk)
      gs
      syms
      pc
      mdl
    )
    s ->
    exists d c' cs',
      (find_function mdl (ic_fid ic')) = Some d /\
      (get_trailing_cmds d ic') = Some (c' :: cs') /\
      s = (mk_sym_state
        ic'
        c'
        cs'
        pbid'
        ls'
        stk
        gs
        syms
        pc
        mdl
      ).
Proof.
  intros ic cid pbid ls ls' ic' pbid' stk gs syms pc mdl s Hstep.
  inversion Hstep; subst.
  exists d, c', cs'.
  split; try assumption.
  split; try assumption.
  reflexivity.
Qed.
