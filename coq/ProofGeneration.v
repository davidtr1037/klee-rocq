From Coq Require Import List.
From Coq Require Import Logic.Eqdep.

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

Lemma injection_ast : forall (sort : smt_sort) (ast1 ast2 : smt_ast sort),
  Expr sort ast1 = Expr sort ast2 ->
  ast1 = ast2.
Proof.
  intros sort ast1 ast2 H.
  inversion H.
  apply inj_pair2.
  assumption.
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
