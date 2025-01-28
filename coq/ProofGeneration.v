From Coq Require Import Bool.
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

From SE.Numeric Require Import Integers.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

From SE.Utils Require Import IDMap.
From SE.Utils Require Import Util.

Lemma injection_expr : forall (sort : smt_sort) (ast1 ast2 : smt_ast sort),
  Expr sort ast1 = Expr sort ast2 ->
  ast1 = ast2.
Proof.
  intros sort ast1 ast2 H.
  inversion H.
  apply inj_pair2.
  assumption.
Qed.

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

Lemma sat_unsat_contradiction : forall ast,
  sat ast ->
  unsat ast ->
  False.
Proof.
  intros ast Hsat Hunsat.
  unfold unsat in Hunsat.
  unfold not in Hunsat.
  apply Hunsat.
  assumption.
Qed.

Lemma not_error_instr_op : forall ic cid v e cs pbid ls stk gs syms pc mdl,
  is_supported_exp e ->
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
  intros ic cid v e cs pbid ls stk gs syms pc mdl His.
  intros Herr.
  inversion Herr; subst.
  { inversion His; subst. inversion H2; subst; inversion H6. }
  { inversion His; subst. inversion H3; subst; inversion H6. }
  { inversion His; subst. inversion H2; subst; inversion H6. }
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

Lemma equiv_smt_store_on_update_via_some : forall s v se1 se2 se3,
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

Lemma equiv_smt_store_on_update : forall s v se1 se2,
  equiv_smt_expr se1 se2 ->
  equiv_smt_store (v !-> Some se1; s) (v !-> Some se2; s).
Proof.
  intros s v se1 se2 Heq.
  apply equiv_smt_store_update.
  { apply equiv_smt_store_refl. }
  { assumption. }
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
      { apply equiv_smt_expr_not_not. }
    }
    { assumption. }
  }
  { assumption. }
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

Lemma safe_subtree_instr_op_generic : forall ic cid v e c cs pbid ls stk gs syms pc mdl ls_opt t,
  let s_init :=
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
    ) in
  equiv_smt_store (v !-> (sym_eval_exp ls gs None e); ls) ls_opt ->
  (root t =
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
    )
  ) ->
  ~ error_sym_state s_init ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v e c cs pbid ls stk gs syms pc mdl ls_opt t.
  intros s_init Heq Ht Hne Hsafe.
  apply Safe_Subtree.
  { assumption. }
  {
    intros s' Hstep.
    left.
    exists t.
    split.
    { apply in_list_0. }
    {
      split.
      { assumption. }
      {
        apply inversion_instr_op in Hstep.
        destruct Hstep as [se [Heval Hs]].
        rewrite Hs.
        rewrite Ht.
        apply EquivSymState.
        {
          rewrite <- Heval.
          assumption.
        }
        { apply equiv_sym_stack_refl. }
        { apply equiv_smt_store_refl. }
        { apply equiv_smt_expr_refl. }
      }
    }
  }
Qed.

Lemma safe_subtree_instr_op : forall ic cid v e c cs pbid ls stk gs syms pc mdl ls_opt t,
  let s_init :=
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
    ) in
  is_supported_exp e ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None e); ls) ls_opt ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v e c cs pbid ls stk gs syms pc mdl ls_opt t.
  intros s_init His Heq Ht Hsafe.
  eapply safe_subtree_instr_op_generic; try eassumption.
  apply not_error_instr_op.
  assumption.
Qed.

Lemma safe_subtree_instr_op_division : forall ic cid v op et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop op et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_unsafe_division_non_sdiv op ->
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop op et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  unsat (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition se2)) ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v op et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 t.
  intros s_init Hop His1 His2 Heq Heval_e2 Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_generic; try eassumption.
  intros Herr.
  inversion Herr; subst.
  {
    rewrite Heval_e2 in H15.
    inversion H15; subst.
    unfold unsat in Hunsat.
    apply Hunsat.
    assumption.
  }
  { inversion Hop. }
  { inversion Hop; inversion H2; subst; try discriminate. }
Qed.

Definition sym_division_error_condition_opt se :=
  match se with
  | Expr sort ast =>
      (AST_CmpOp Sort_BV64 SMT_Eq (AST_Const Sort_BV64 (repr 0)) (AST_ZExt sort ast Sort_BV64))
  end
.

Lemma equiv_smt_expr_division_error_condition : forall se,
  equiv_smt_expr
    (Expr Sort_BV1 (sym_division_error_condition se))
    (Expr Sort_BV1 (sym_division_error_condition_opt se)).
Proof.
  intros se.
  destruct se as [sort ast].
  simpl.
  apply EquivExpr.
  intros m.
  simpl.
  destruct sort; unfold smt_eval_cmpop_by_sort; unfold smt_eval_cmpop_generic; simpl.
  {
    rewrite eq_zero_zext_i1_i64.
    rewrite Int64.eq_sym.
    reflexivity.
  }
  {
    rewrite eq_zero_zext_i8_i64.
    rewrite Int64.eq_sym.
    reflexivity.
  }
  {
    rewrite eq_zero_zext_i16_i64.
    rewrite Int64.eq_sym.
    reflexivity.
  }
  {
    rewrite eq_zero_zext_i32_i64.
    rewrite Int64.eq_sym.
    reflexivity.
  }
  {
    rewrite Int64.repr_unsigned.
    rewrite Int64.eq_sym.
    reflexivity.
  }
Qed.

(* used in the non-optimized mode *)
Lemma unsat_sym_division_error_condition : forall pc se cond,
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition_opt se)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  unsat (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition se)).
Proof.
  intros pc se cond Heq Hunsat.
  eapply equiv_smt_expr_unsat.
  {
    apply equiv_smt_expr_symmetry.
    eapply equiv_smt_expr_binop.
    { apply equiv_smt_expr_refl. }
    { apply equiv_smt_expr_division_error_condition. }
  }
  {
    eapply equiv_smt_expr_unsat.
    {
      apply equiv_smt_expr_symmetry.
      eassumption.
    }
    { assumption. }
  }
Qed.

Lemma safe_subtree_instr_op_division_opt : forall ic cid v op et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop op et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_unsafe_division_non_sdiv op ->
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop op et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition_opt se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v op et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t.
  intros s_init Hop His1 His2 Heq Heval_e2 Hcond Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_division; try eassumption.
  eapply equiv_smt_expr_unsat.
  {
    eapply equiv_smt_expr_transitivity.
    { eapply equiv_smt_expr_symmetry. apply Hcond. }
    {
      eapply equiv_smt_expr_symmetry.
      apply equiv_smt_expr_binop.
      { apply equiv_smt_expr_refl. }
      { apply equiv_smt_expr_division_error_condition. }
    }
  }
  { assumption. }
Qed.

Lemma safe_subtree_instr_op_udiv : forall ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop (UDiv false) et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop (UDiv false) et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition_opt se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t.
  intros s_init His1 His2 Heq Heval_e2 Hcond Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_division_opt; try eassumption.
  apply Is_Unsafe_Division_Non_SDiv_UDiv.
Qed.

Lemma safe_subtree_instr_op_urem : forall ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop URem et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop URem et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition_opt se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t.
  intros s_init His1 His2 Heq Heval_e2 Hcond Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_division_opt; try eassumption.
  apply Is_Unsafe_Division_Non_SDiv_URem.
Qed.

Lemma safe_subtree_instr_op_srem : forall ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop SRem et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop SRem et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition_opt se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t.
  intros s_init His1 His2 Heq Heval_e2 Hcond Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_division_opt; try eassumption.
  apply Is_Unsafe_Division_Non_SDiv_SRem.
Qed.

Definition sym_sdiv_error_condition_opt se1 se2 :=
  match se1, se2 with
  | Expr Sort_BV32 ast1, Expr Sort_BV32 ast2 =>
      AST_CmpOp
        Sort_BV1
        SMT_Eq
        smt_ast_false
        (AST_BinOp
          Sort_BV1
          SMT_And
          (AST_BinOp
            Sort_BV1
            SMT_Or
              (AST_CmpOp
                Sort_BV1
                SMT_Eq
                smt_ast_false
                (AST_CmpOp Sort_BV32 SMT_Eq (AST_Const Sort_BV32 (repr 2147483648)) ast1))
              (AST_CmpOp
                Sort_BV1
                SMT_Eq
                smt_ast_false
                (AST_CmpOp Sort_BV32 SMT_Eq (AST_Const Sort_BV32 (repr 4294967295)) ast2)))
          (AST_CmpOp
            Sort_BV1
            SMT_Eq
            smt_ast_false
            (AST_CmpOp Sort_BV32 SMT_Eq (AST_Const Sort_BV32 (repr 0)) ast2)))
  (* TODO: just for making the related proofs easier *)
  | _, _ => smt_ast_true
  end
.

Lemma sym_sdiv_error_condition_opt_guarantees : forall pc se1 se2,
  unsat (AST_BinOp Sort_BV1 SMT_And pc (sym_sdiv_error_condition_opt se1 se2)) ->
  (
    unsat (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition se2)) /\
    unsat (AST_BinOp Sort_BV1 SMT_And pc (sym_division_overflow_error_condition se1 se2))
  ).
Proof.
  intros pc se1 se2 Hunsat.
  split.
  {
    intros Hsat.
    apply Hunsat.
    simpl.
    destruct se1 as [sort1 ast1], se2 as [sort2 ast2].
    destruct sort1, sort2;
    try (
      simpl;
      destruct Hsat as [m Hsat];
      apply sat_and_left in Hsat;
      exists m;
      apply sat_intro_and; [
        assumption |
        reflexivity
      ]
    ).
    {
      simpl.
      simpl in Hsat.
      destruct Hsat as [m Hsat].
      exists m.
      apply sat_intro_and.
      {
        apply sat_and_left in Hsat.
        assumption.
      }
      {
        eapply equiv_smt_expr_sat_via.
        { eapply equiv_smt_expr_not_rewrite. }
        {
          eapply equiv_smt_expr_sat_via.
          {
            eapply equiv_smt_expr_symmetry.
            eapply equiv_smt_expr_de_morgan_and.
          }
          {
            apply sat_intro_or_right.
            eapply equiv_smt_expr_sat_via.
            {
              eapply equiv_smt_expr_not.
              { apply equiv_smt_expr_not_rewrite. }
            }
            {
              eapply equiv_smt_expr_sat_via.
              {
                eapply equiv_smt_expr_symmetry.
                apply equiv_smt_expr_not_not.
              }
              {
                apply sat_and_right in Hsat.
                eapply equiv_smt_expr_sat_via.
                {
                  eapply equiv_smt_expr_symmetry.
                  eapply equiv_smt_expr_eq_symmetry.
                }
                { assumption. }
              }
            }
          }
        }
      }
    }
  }
  {
    intros Hsat.
    apply Hunsat.
    simpl.
    destruct se1 as [sort1 ast1], se2 as [sort2 ast2].
    destruct sort1, sort2;
    try (
      simpl;
      destruct Hsat as [m Hsat];
      apply sat_and_left in Hsat;
      exists m;
      apply sat_intro_and; [
        assumption |
        reflexivity
      ]
    ).
    {
      simpl.
      simpl in Hsat.
      destruct Hsat as [m Hsat].
      exists m.
      apply sat_intro_and.
      {
        apply sat_and_left in Hsat.
        assumption.
      }
      {
        eapply equiv_smt_expr_sat_via.
        { eapply equiv_smt_expr_not_rewrite. }
        {
          eapply equiv_smt_expr_sat_via.
          {
            eapply equiv_smt_expr_symmetry.
            eapply equiv_smt_expr_de_morgan_and.
          }
          {
            apply sat_intro_or_left.
            eapply equiv_smt_expr_sat_via.
            {
              eapply equiv_smt_expr_symmetry.
              eapply equiv_smt_expr_de_morgan_or.
            }
            {
              apply sat_intro_and.
              {
                eapply equiv_smt_expr_sat_via.
                {
                  eapply equiv_smt_expr_not.
                  { apply equiv_smt_expr_not_rewrite. }
                }
                {
                  eapply equiv_smt_expr_sat_via.
                  {
                    eapply equiv_smt_expr_symmetry.
                    apply equiv_smt_expr_not_not.
                  }
                  {
                    apply sat_and_right in Hsat.
                    apply sat_and_left in Hsat.
                    eapply equiv_smt_expr_sat_via.
                    { eapply equiv_smt_expr_eq_symmetry. }
                    { assumption. }
                  }
                }
              }
              {
                eapply equiv_smt_expr_sat_via.
                {
                  eapply equiv_smt_expr_not.
                  { apply equiv_smt_expr_not_rewrite. }
                }
                {
                  eapply equiv_smt_expr_sat_via.
                  {
                    eapply equiv_smt_expr_symmetry.
                    apply equiv_smt_expr_not_not.
                  }
                  {
                    apply sat_and_right in Hsat.
                    apply sat_and_right in Hsat.
                    eapply equiv_smt_expr_sat_via.
                    { eapply equiv_smt_expr_eq_symmetry. }
                    { assumption. }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
Qed.

(* used in the non-optimized mode *)
Lemma unsat_sym_sdiv_division_error_condition : forall pc se1 se2 cond,
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_sdiv_error_condition_opt se1 se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  unsat (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition se2)).
Proof.
  intros pc se1 se2 cond Heq Hunsat.
  apply equiv_smt_expr_symmetry in Heq.
  apply equiv_smt_expr_unsat in Heq; try assumption.
  apply sym_sdiv_error_condition_opt_guarantees in Heq.
  destruct Heq as [Heq _].
  assumption.
Qed.

(* used in the non-optimized mode *)
Lemma unsat_sym_sdiv_overflow_error_condition : forall pc se1 se2 cond,
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_sdiv_error_condition_opt se1 se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  unsat (AST_BinOp Sort_BV1 SMT_And pc (sym_division_overflow_error_condition se1 se2)).
Proof.
  intros pc se1 se2 cond Heq Hunsat.
  apply equiv_smt_expr_symmetry in Heq.
  apply equiv_smt_expr_unsat in Heq; try assumption.
  apply sym_sdiv_error_condition_opt_guarantees in Heq.
  destruct Heq as [_ Heq].
  assumption.
Qed.

Lemma safe_subtree_instr_op_sdiv : forall ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se1 se2 cond t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop (SDiv false) et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop (SDiv false) et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e1 = Some se1 ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_sdiv_error_condition_opt se1 se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se1 se2 cond t.
  intros s_init His1 His2 Heq Heval_e1 Heval_e2 Hcond Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_generic; try eassumption.
  apply equiv_smt_expr_symmetry in Hcond.
  apply equiv_smt_expr_unsat in Hcond; try assumption.
  intros Herr.
  inversion Herr; subst.
  {
    rewrite Heval_e2 in H15.
    inversion H15; subst.
    rename se into se2.
    apply sym_sdiv_error_condition_opt_guarantees in Hcond.
    destruct Hcond as [Hcond _].
    apply Hcond.
    assumption.
  }
  {
    rewrite Heval_e1 in H2.
    rewrite Heval_e2 in H15.
    inversion H2; subst.
    inversion H15; subst.
    rename se0 into se1, se3 into se2.
    apply sym_sdiv_error_condition_opt_guarantees in Hcond.
    destruct Hcond as [_ Hcond].
    apply Hcond.
    assumption.
  }
  { inversion H2. }
Qed.

Lemma safe_subtree_instr_op_shift : forall ic cid v op et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop op et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_unsafe_shift op ->
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop op et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  unsat (AST_BinOp Sort_BV1 SMT_And pc (sym_shift_error_condition se2)) ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v op et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 t.
  intros s_init Hop His1 His2 Heq Heval_e2 Hunsat Ht Hsafe.
  apply Safe_Subtree.
  {
    intros Herr.
    inversion Herr; subst.
    { inversion Hop; subst; inversion H2. }
    { inversion Hop. }
    {
      rewrite Heval_e2 in H15.
      inversion H15; subst.
      unfold unsat in Hunsat.
      apply Hunsat.
      assumption.
    }
  }
  {
    intros s' Hstep.
    left.
    exists t.
    split.
    { apply in_list_0. }
    {
      split.
      { assumption. }
      {
        apply inversion_instr_op in Hstep.
        destruct Hstep as [se [Heval Hs]].
        rewrite Hs.
        rewrite Ht.
        apply EquivSymState.
        {
          rewrite <- Heval.
          assumption.
        }
        { apply equiv_sym_stack_refl. }
        { apply equiv_smt_store_refl. }
        { apply equiv_smt_expr_refl. }
      }
    }
  }
Qed.

Definition sym_shift_error_condition_opt se :=
  match se with
  | Expr sort ast =>
     (AST_CmpOp
        Sort_BV1
        SMT_Eq
        (AST_Const Sort_BV1 zero)
        (AST_CmpOp
          Sort_BV64
          SMT_Ult
          (AST_ZExt sort ast Sort_BV64)
          (AST_Const Sort_BV64 (create_int_by_sort Sort_BV64 (Zpos (smt_sort_to_width sort))))))
  end
.

Lemma equiv_smt_expr_shift_error_condition : forall se,
  equiv_smt_expr
    (Expr Sort_BV1 (sym_shift_error_condition se))
    (Expr Sort_BV1 (sym_shift_error_condition_opt se)).
Proof.
  intros se.
  destruct se as [sort ast].
  simpl.
  apply EquivExpr.
  intros m.
  simpl.
  remember (smt_eval_ast m sort ast) as n.
  destruct sort; unfold smt_eval_cmpop_by_sort; unfold smt_eval_cmpop_generic; simpl.
  {
    rewrite <- ltu_zext_i1_i64.
    destruct (Int1.ltu n (Int1.repr 1)); reflexivity.
  }
  {
    rewrite <- ltu_zext_i8_i64.
    destruct (Int8.ltu n (Int8.repr 8)); reflexivity.
  }
  {
    rewrite <- ltu_zext_i16_i64.
    destruct (Int16.ltu n (Int16.repr 16)); reflexivity.
  }
  {
    rewrite <- ltu_zext_i32_i64.
    destruct (Int32.ltu n (Int32.repr 32)); reflexivity.
  }
  {
    rewrite Int64.repr_unsigned.
    destruct (Int64.ltu n (Int64.repr 64)); reflexivity.
  }
Qed.

(* used in the non-optimized mode *)
Lemma unsat_sym_shift_error_condition : forall pc se cond,
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_shift_error_condition_opt se)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  unsat (AST_BinOp Sort_BV1 SMT_And pc (sym_shift_error_condition se)).
Proof.
  intros pc se cond Heq Hunsat.
  eapply equiv_smt_expr_unsat.
  {
    apply equiv_smt_expr_symmetry.
    eapply equiv_smt_expr_binop.
    { apply equiv_smt_expr_refl. }
    { apply equiv_smt_expr_shift_error_condition. }
  }
  {
    eapply equiv_smt_expr_unsat.
    {
      apply equiv_smt_expr_symmetry.
      eassumption.
    }
    { assumption. }
  }
Qed.

Lemma safe_subtree_instr_op_shift_opt : forall ic cid v op et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop op et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_unsafe_shift op ->
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop op et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_shift_error_condition_opt se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v op et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t.
  intros s_init Hop His1 His2 Heq Heval_e2 Hcond Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_shift; try eassumption.
  eapply equiv_smt_expr_unsat.
  {
    eapply equiv_smt_expr_transitivity.
    { eapply equiv_smt_expr_symmetry. apply Hcond. }
    {
      eapply equiv_smt_expr_symmetry.
      apply equiv_smt_expr_binop.
      { apply equiv_smt_expr_refl. }
      { apply equiv_smt_expr_shift_error_condition. }
    }
  }
  { assumption. }
Qed.

Lemma safe_subtree_instr_op_shl : forall ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop (Shl false false) et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop (Shl false false) et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_shift_error_condition_opt se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t.
  intros s_init His1 His2 Heq Heval_e2 Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_shift_opt; try eassumption.
  apply Is_Unsafe_Shift_Shl.
Qed.

Lemma safe_subtree_instr_op_lshr : forall ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop (LShr false) et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop (LShr false) et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_shift_error_condition_opt se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t.
  intros s_init His1 His2 Heq Heval_e2 Hcond Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_shift_opt; try eassumption.
  apply Is_Unsafe_Shift_LShr.
Qed.

Lemma safe_subtree_instr_op_ashr : forall ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Op v (OP_IBinop (AShr false) et e1 e2)))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  is_supported_exp e1 ->
  is_supported_exp e2 ->
  equiv_smt_store (v !-> (sym_eval_exp ls gs None (OP_IBinop (AShr false) et e1 e2)); ls) ls_opt ->
  sym_eval_exp ls gs (Some et) e2 = Some se2 ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (sym_shift_error_condition_opt se2)))
    (Expr Sort_BV1 cond) ->
  unsat cond ->
  (root t =
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v et e1 e2 c cs pbid ls stk gs syms pc mdl ls_opt se2 cond t.
  intros s_init His1 His2 Heq Heval_e2 Hcond Hunsat Ht Hsafe.
  eapply safe_subtree_instr_op_shift_opt; try eassumption.
  apply Is_Unsafe_Shift_AShr.
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

Lemma safe_subtree_phi : forall ic cid v argtype args c cs pbid ls stk gs syms pc mdl ls_opt t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Phi cid (Phi v argtype args))
      (c :: cs)
      (Some pbid)
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  equiv_smt_store (v !-> (sym_eval_phi_args ls gs argtype args pbid); ls) ls_opt ->
  (root t =
    (mk_sym_state
      (next_inst_counter ic c)
      c
      cs
      (Some pbid)
      ls_opt
      stk
      gs
      syms
      pc
      mdl
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v argtype args c cs pbid ls stk gs syms pc mdl ls_opt t.
  intros s_init Heq Ht Hsafe.
  apply Safe_Subtree.
  { apply not_error_phi. }
  {
    intros s' Hstep.
    left.
    exists t.
    split.
    { apply in_list_0. }
    {
      split.
      { assumption. }
      {
        apply inversion_phi in Hstep.
        destruct Hstep as [se [Heval Hs]].
        rewrite Hs.
        rewrite Ht.
        apply EquivSymState.
        {
          rewrite <- Heval.
          assumption.
        }
        { apply equiv_sym_stack_refl. }
        { apply equiv_smt_store_refl. }
        { apply equiv_smt_expr_refl. }
      }
    }
  }
Qed.

Lemma equiv_sym_state_phi : forall ic cid v t args c cs pbid ls stk gs syms pc mdl ls_opt s,
  equiv_smt_store (v !-> (sym_eval_phi_args ls gs t args pbid); ls) ls_opt ->
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
    equiv_sym_state
      s
      (mk_sym_state
        (next_inst_counter ic c)
        c
        cs
        (Some pbid)
        ls_opt
        stk
        gs
        syms
        pc
        mdl
      ).
Proof.
  intros ic cid v t args c cs pbid ls stk gs syms pc mdl ls_opt s Heq Hstep.
  apply inversion_phi in Hstep.
  destruct Hstep as [se [Heval Hs]].
  subst.
  rewrite Heval in Heq.
  apply EquivSymState.
  { assumption. }
  { apply equiv_sym_stack_refl. }
  { apply equiv_smt_store_refl. }
  { apply equiv_smt_expr_refl. }
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

Lemma safe_subtree_unconditional_br : forall ic cid tbid pbid ls stk gs syms pc mdl d b c cs t,
  let s_init :=
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
    ) in
  (find_function mdl (ic_fid ic)) = Some d ->
  (fetch_block d tbid) = Some b ->
  (blk_cmds b) = c :: cs ->
  (root t =
    (mk_sym_state
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid tbid pbid ls stk gs syms pc mdl d b c cs t s_init Hd Hb Hcs.
  intros Ht Hsafe.
  apply Safe_Subtree.
  { apply not_error_unconditional_br. }
  {
    intros s' Hstep.
    left.
    exists t.
    split.
    { apply in_list_0. }
    {
      split.
      { assumption. }
      {
        apply inversion_unconditional_br in Hstep.
        destruct  Hstep as [d' [b' [c' [cs' [Hd' [Hb' [Hcs' Hs]]]]]]].
        rewrite Hd' in Hd.
        inversion Hd; subst.
        rewrite Hb' in Hb.
        inversion Hb; subst.
        rewrite Hcs' in Hcs.
        inversion Hcs; subst.
        rewrite Ht.
        apply EquivSymState.
        { apply equiv_smt_store_refl. }
        { apply equiv_sym_stack_refl. }
        { apply equiv_smt_store_refl. }
        { apply equiv_smt_expr_refl. }
      }
    }
  }
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

Definition extract_smt_expr (ose : option smt_expr) : smt_expr :=
  match ose with
  | Some se => se
  | None => smt_expr_false
  end
.

(* TODO: rename *)
Definition extract_ast (se : option smt_expr) : (smt_ast Sort_BV1) :=
  match se with
  | Some se =>
      match se with
      | Expr Sort_BV1 ast => ast
      | _ => smt_ast_false
      end
  | None => smt_ast_false
  end
.

Lemma safe_subtree_br_sat_unsat : forall ic cid e bid1 bid2 pbid ls stk gs syms pc mdl cond d b1 c1 cs1 pc1 pc2 t,
  let s_init :=
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
    ) in
  (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some (Expr Sort_BV1 cond) ->
  (find_function mdl (ic_fid ic)) = Some d ->
  (fetch_block d bid1) = Some b1 ->
  (blk_cmds b1) = c1 :: cs1 ->
  (root t =
    (mk_sym_state
      (mk_inst_counter (ic_fid ic) bid1 (get_cmd_id c1))
      c1
      cs1
      (Some (ic_bid ic))
      ls
      stk
      gs
      syms
      pc1
      mdl
    )
  ) ->
  (safe_et_opt t) ->
  (equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc cond))
    (Expr Sort_BV1 pc1)
  ) ->
  (equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (AST_Not Sort_BV1 cond)))
    (Expr Sort_BV1 pc2)
  ) ->
  unsat pc2 ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid e bid1 bid2 pbid ls stk gs syms pc mdl cond d b1 c1 cs1 pc1 pc2 t.
  intros s_init Heval Hd Hb1 Hcs1 Ht Hsafe Heq1 Heq2 Hunsat2.
  apply Safe_Subtree.
  { apply not_error_br. }
  {
    intros s' Hstep.
    apply inversion_br in Hstep.
    destruct Hstep as [cond' [d' [b' [c' [cs' [Heval' [Hd' H]]]]]]].
    rewrite Heval' in Heval.
    apply injection_some in Heval.
    apply injection_expr in Heval.
    subst.
    rewrite Hd' in Hd.
    inversion Hd; subst.
    destruct H as [H | H].
    {
      left.
      destruct H as [Hb' [Hcs' Hs]].
      rewrite Hb' in Hb1.
      inversion Hb1; subst.
      rewrite Hcs' in Hcs1.
      inversion Hcs1; subst.
      exists t.
      split.
      { apply in_list_0. }
      {
        split.
        { assumption. }
        {
          rewrite Ht.
          apply EquivSymState.
          { apply equiv_smt_store_refl. }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { assumption. }
        }
      }
    }
    {
      right.
      destruct H as [Hb' [Hcs' Hs]].
      rewrite Hs.
      apply Unsat_State.
      apply equiv_smt_expr_unsat with (ast1 := pc2).
      {
        apply equiv_smt_expr_symmetry.
        assumption.
      }
      { assumption. }
    }
  }
Qed.

Lemma safe_subtree_br_unsat_sat : forall ic cid e bid1 bid2 pbid ls stk gs syms pc mdl cond d b2 c2 cs2 pc2 pc1 t,
  (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some (Expr Sort_BV1 cond) ->
  (find_function mdl (ic_fid ic)) = Some d ->
  (fetch_block d bid2) = Some b2 ->
  (blk_cmds b2) = c2 :: cs2 ->
  let s_init :=
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
    ) in
  (root t =
    (mk_sym_state
      (mk_inst_counter (ic_fid ic) bid2 (get_cmd_id c2))
      c2
      cs2
      (Some (ic_bid ic))
      ls
      stk
      gs
      syms
      pc2
      mdl
    )
  ) ->
  (safe_et_opt t) ->
  (equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (AST_Not Sort_BV1 cond)))
    (Expr Sort_BV1 pc2)
  ) ->
  (equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc cond))
    (Expr Sort_BV1 pc1)
  ) ->
  unsat pc1 ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid e bid1 bid2 pbid ls stk gs syms pc mdl cond d b2 c2 cs2 pc2 pc1 t.
  intros Heval Hd Hb2 Hcs2 s_init Ht Hsafe Heq2 Heq1 Hunsat1.
  apply Safe_Subtree.
  { apply not_error_br. }
  {
    intros s' Hstep.
    apply inversion_br in Hstep.
    destruct Hstep as [cond' [d' [b' [c' [cs' [Heval' [Hd' H]]]]]]].
    rewrite Heval' in Heval.
    apply injection_some in Heval.
    apply injection_expr in Heval.
    subst.
    rewrite Hd' in Hd.
    inversion Hd; subst.
    destruct H as [H | H].
    {
      right.
      destruct H as [Hb' [Hcs' Hs]].
      rewrite Hs.
      apply Unsat_State.
      apply equiv_smt_expr_unsat with (ast1 := pc1).
      {
        apply equiv_smt_expr_symmetry.
        assumption.
      }
      { assumption. }
    }
    {
      left.
      destruct H as [Hb' [Hcs' Hs]].
      rewrite Hb' in Hb2.
      inversion Hb2; subst.
      rewrite Hcs' in Hcs2.
      inversion Hcs2; subst.
      exists t.
      split.
      { apply in_list_0. }
      {
        split.
        { assumption. }
        {
          rewrite Ht.
          apply EquivSymState.
          { apply equiv_smt_store_refl. }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { assumption. }
        }
      }
    }
  }
Qed.

Lemma safe_subtree_br_fork : forall ic cid e bid1 bid2 pbid ls stk gs syms pc mdl cond d b1 c1 cs1 pc1 b2 c2 cs2 pc2 t1 t2,
  let s_init :=
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
    ) in
  (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some (Expr Sort_BV1 cond) ->
  (find_function mdl (ic_fid ic)) = Some d ->
  (fetch_block d bid1) = Some b1 ->
  (blk_cmds b1) = c1 :: cs1 ->
  (fetch_block d bid2) = Some b2 ->
  (blk_cmds b2) = c2 :: cs2 ->
  (root t1 =
    (mk_sym_state
      (mk_inst_counter (ic_fid ic) bid1 (get_cmd_id c1))
      c1
      cs1
      (Some (ic_bid ic))
      ls
      stk
      gs
      syms
      pc1
      mdl
    )
  ) ->
  (safe_et_opt t1) ->
  (equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc cond))
    (Expr Sort_BV1 pc1)
  ) ->
  (root t2 =
    (mk_sym_state
      (mk_inst_counter (ic_fid ic) bid2 (get_cmd_id c2))
      c2
      cs2
      (Some (ic_bid ic))
      ls
      stk
      gs
      syms
      pc2
      mdl
    )
  ) ->
  (safe_et_opt t2) ->
  (equiv_smt_expr
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_And pc (AST_Not Sort_BV1 cond)))
    (Expr Sort_BV1 pc2)
  ) ->
  (safe_et_opt (t_subtree s_init [t1; t2])).
Proof.
  intros ic cid e bid1 bid2 pbid ls stk gs syms pc mdl cond d b1 c1 cs1 pc1 b2 c2 cs2 pc2 t1 t2.
  intros s_init Heval Hd Hb1 Hcs1 Hb2 Hcs2 Ht1 Hsafe1 Heq1 Ht2 Hsafe2 Heq2. 
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s' Hstep.
    apply inversion_br in Hstep.
    destruct Hstep as [cond' [d' [b' [c' [cs' [Heval' [Hd' H]]]]]]].
    rewrite Heval' in Heval.
    apply injection_some in Heval.
    apply injection_expr in Heval.
    subst.
    rewrite Hd' in Hd.
    inversion Hd; subst.
    destruct H as [H | H].
    {
      left.
      exists t1.
      split.
      { apply in_list_0. }
      {
        split.
        { assumption. }
        {
          destruct H as [Hb1' [Hcs1' Hs]].
          rewrite Hb1' in Hb1.
          inversion Hb1; subst.
          rewrite Hcs1' in Hcs1.
          inversion Hcs1; subst.
          rewrite Ht1.
          apply EquivSymState.
          { apply equiv_smt_store_refl. }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { assumption. }
        }
      }
    }
    {
      left.
      exists t2.
      split.
      { apply in_list_1. }
      {
        split.
        { assumption. }
        {
          destruct H as [Hb2' [Hcs2' Hs]].
          rewrite Hb2' in Hb2.
          inversion Hb2; subst.
          rewrite Hcs2' in Hcs2.
          inversion Hcs2; subst.
          rewrite Ht2.
          apply EquivSymState.
          { apply equiv_smt_store_refl. }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { assumption. }
        }
      }
    }
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

Lemma safe_subtree_call : forall ic cid v ftype f args anns c cs pbid ls stk gs syms pc mdl d b c' cs' ls' t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Inst cid (INSTR_Call v (ftype, f) args anns))
      (c :: cs)
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ) in
  (find_function_by_exp mdl f) = Some d ->
  (dc_type (df_prototype d)) = TYPE_Function ftype (get_arg_types args) false ->
  (entry_block d) = Some b ->
  (blk_cmds b) = c' :: cs' ->
  (create_local_smt_store d ls gs args) = Some ls' ->
  (root t =
    (mk_sym_state
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid v ftype f args anns c cs pbid ls stk gs syms pc mdl d b c' cs' ls' t.
  intros s_init Hd Hdc Hb Hcs Hls Ht Hsafe.
  apply Safe_Subtree.
  { apply not_error_call. }
  {
    intros s' Hstep.
    left.
    exists t.
    split.
    { apply in_list_0. }
    {
      split.
      { assumption. }
      {
        apply inversion_call with (d := d) in Hstep.
        {
          destruct Hstep as [b' [c'' [cs'' [ls'' [Hdc' [Hb' [Hcs' [Hls' Hs]]]]]]]].
          rewrite Hs.
          rewrite Ht.
          rewrite Hb' in Hb.
          inversion Hb; subst.
          rewrite Hcs' in Hcs.
          inversion Hcs; subst.
          rewrite Hls' in Hls.
          inversion Hls; subst.
          apply EquivSymState.
          { apply equiv_smt_store_refl. }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
        { assumption. }
      }
    }
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

Lemma safe_subtree_void_call : forall ic cid f args anns c cs pbid ls stk gs syms pc mdl d b c' cs' ls' t,
  let s_init :=
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
    ) in
  f <> assert_exp ->
  (find_function_by_exp mdl f) = Some d ->
  (dc_type (df_prototype d)) = TYPE_Function TYPE_Void (get_arg_types args) false ->
  (entry_block d) = Some b ->
  (blk_cmds b) = c' :: cs' ->
  (create_local_smt_store d ls gs args) = Some ls' ->
  (root t =
    (mk_sym_state
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid f args anns c cs pbid ls stk gs syms pc mdl d b c' cs' ls' t.
  intros s_init Hf Hd Hdc Hb Hcs Hls Ht Hsafe.
  apply Safe_Subtree.
  {
    apply not_error_void_call.
    intros H.
    inversion H; subst.
    apply Hf.
    reflexivity.
  }
  {
    intros s' Hstep.
    left.
    exists t.
    split.
    { apply in_list_0. }
    {
      split.
      { assumption. }
      {
        apply inversion_void_call with (d := d) in Hstep.
        {
          destruct Hstep as [b' [c'' [cs'' [ls'' [Hdc' [Hb' [Hcs' [Hls' Hs]]]]]]]].
          rewrite Hs.
          rewrite Ht.
          rewrite Hb' in Hb.
          inversion Hb; subst.
          rewrite Hcs' in Hcs.
          inversion Hcs; subst.
          rewrite Hls' in Hls.
          inversion Hls; subst.
          apply EquivSymState.
          { apply equiv_smt_store_refl. }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
        { assumption. }
      }
    }
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

Lemma safe_subtree_ret : forall ic cid rtype e pbid ls ls' ic' pbid' v stk gs syms pc mdl d c' cs' ls_opt t,
  let s_init :=
    (mk_sym_state
      ic
      (CMD_Term cid (TERM_Ret (rtype, e)))
      []
      pbid
      ls
      ((Sym_Frame ls' ic' pbid' (Some v)) :: stk)
      gs
      syms
      pc
      mdl
    ) in
  equiv_smt_store (v !-> (sym_eval_exp ls gs (Some rtype) e); ls') ls_opt ->
  (find_function mdl (ic_fid ic')) = Some d ->
  (get_trailing_cmds d ic') = Some (c' :: cs') ->
  (root t =
    (mk_sym_state
      ic'
      c'
      cs'
      pbid'
      ls_opt
      stk
      gs
      syms
      pc
      mdl
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid rtype e pbid ls ls' ic' pbid' v stk gs syms pc mdl d c' cs' ls_opt t.
  intros s_init Heq Hd Hcs Ht Hsafe.
  apply Safe_Subtree.
  {
    apply not_error_ret.
  }
  {
    intros s' Hstep.
    left.
    exists t.
    split.
    { apply in_list_0. }
    {
      split.
      { assumption. }
      {
        apply inversion_ret in Hstep.
        destruct Hstep as [se [d' [c'' [cs'' [Heval [Hd' [Hcs' Hs]]]]]]].
        rewrite Hs.
        rewrite Ht.
        rewrite Hd' in Hd.
        inversion Hd; subst.
        rewrite Hcs' in Hcs.
        inversion Hcs; subst.
        rewrite <- Heval.
        apply EquivSymState.
        { assumption. }
        { apply equiv_sym_stack_refl. }
        { apply equiv_smt_store_refl. }
        { apply equiv_smt_expr_refl. }
      }
    }
  }
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

Lemma safe_subtree_ret_void : forall ic cid pbid ls ls' ic' pbid' stk gs syms pc mdl d c' cs' t,
  let s_init :=
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
    ) in
  (find_function mdl (ic_fid ic')) = Some d ->
  (get_trailing_cmds d ic') = Some (c' :: cs') ->
  (root t =
    (mk_sym_state
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
    )
  ) ->
  (safe_et_opt t) ->
  (safe_et_opt (t_subtree s_init [t])).
Proof.
  intros ic cid pbid ls ls' ic' pbid' stk gs syms pc mdl d c' cs' t.
  intros s_init Hd Hcs Ht Hsafe.
  apply Safe_Subtree.
  {
    apply not_error_ret_void.
  }
  {
    intros s' Hstep.
    left.
    exists t.
    split.
    { apply in_list_0. }
    {
      split.
      { assumption. }
      {
        apply inversion_ret_void in Hstep.
        destruct Hstep as [d' [c'' [cs'' [Hd' [Hcs' Hs]]]]].
        rewrite Hs.
        rewrite Ht.
        rewrite Hd' in Hd.
        inversion Hd; subst.
        rewrite Hcs' in Hcs.
        inversion Hcs; subst.
        apply EquivSymState.
        { apply equiv_smt_store_refl. }
        { apply equiv_sym_stack_refl. }
        { apply equiv_smt_store_refl. }
        { apply equiv_smt_expr_refl. }
      }
    }
  }
Qed.
