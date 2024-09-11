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

From SE.SMT Require Import TypedExpr.
From SE.SMT Require Import TypedModel.

From SE.Utils Require Import IDMap.

(* TODO: rename lemmas *)

Lemma injection_ast : forall (sort : smt_sort) (ast1 ast2 : typed_smt_ast sort),
  TypedSMTExpr sort ast1 = TypedSMTExpr sort ast2 ->
  ast1 = ast2.
Proof.
  intros sort ast1 ast2 H.
  inversion H.
  apply inj_pair2.
  assumption.
Qed.

Lemma LAUX_not_error_instr_op : forall ic cid v e cs pbid ls stk gs syms pc mdl,
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

Lemma LAUX_not_error_phi : forall ic cid v t args cs pbid ls stk gs syms pc mdl,
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

Lemma LAUX_not_error_unconditional_br : forall ic cid bid cs pbid ls stk gs syms pc mdl,
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

Lemma LAUX_not_error_br : forall ic cid e bid1 bid2 cs pbid ls stk gs syms pc mdl,
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

Lemma LAUX_not_error_call : forall ic cid v f args anns cs pbid ls stk gs syms pc mdl,
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

Lemma LAUX_not_error_void_call : forall ic cid f args anns cs pbid ls stk gs syms pc mdl,
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

Lemma LAUX_not_error_ret : forall ic cid e cs pbid ls stk gs syms pc mdl,
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

Lemma LAUX_not_error_ret_void : forall ic cid cs pbid ls stk gs syms pc mdl,
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

Lemma LAUX_1 : forall s v se1 se2 se3,
  Some se1 = Some se2 ->
  equiv_typed_smt_expr se1 se3 ->
  equiv_smt_store (v !-> Some se2; s) (v !-> Some se3; s).
Proof.
  intros s v se1 se2 se3 H Heq.
  inversion H; subst.
  apply equiv_smt_store_update.
  { apply equiv_smt_store_refl. }
  { assumption. }
Qed.

Lemma LAUX_2: forall m x se1 se2 se3 l,
  equiv_typed_smt_expr se2 se3 ->
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
      apply equiv_typed_smt_expr_refl.
    }
    {
      left.
      split; reflexivity.
    }
  }
Qed.

Lemma LAUX_normalize_simplify: forall (sort : smt_sort) (ast : typed_smt_ast sort),
  equiv_typed_smt_expr
    (TypedSMTExpr sort ast)
    (TypedSMTExpr sort (simplify sort (normalize sort ast))).
Proof.
Admitted.

Lemma equiv_smt_expr_implied_condition: forall ast1 ast2,
  unsat (TypedAST_BinOp Sort_BV1 SMT_And ast1 (TypedAST_Not Sort_BV1 ast2)) ->
  equiv_typed_smt_expr
    (TypedSMTExpr Sort_BV1 (TypedAST_BinOp Sort_BV1 SMT_And ast1 ast2))
    (TypedSMTExpr Sort_BV1 ast1).
Proof.
Admitted.

Lemma implied_condition: forall ast1 ast2 ast3,
  equiv_typed_smt_expr
    (TypedSMTExpr Sort_BV1 (TypedAST_BinOp Sort_BV1 SMT_And ast1 (TypedAST_Not Sort_BV1 ast2)))
    (TypedSMTExpr Sort_BV1 ast3) ->
  unsat ast3 ->
  equiv_typed_smt_expr
    (TypedSMTExpr Sort_BV1 (TypedAST_BinOp Sort_BV1 SMT_And ast1 ast2))
    (TypedSMTExpr Sort_BV1 ast1).
Proof.
  intros ast1 ast2 ast3 Heq Hunsat.
  apply equiv_smt_expr_implied_condition.
  apply equiv_typed_smt_expr_unsat with (ast1 := ast3).
  { apply equiv_typed_smt_expr_symmetry. assumption. }
  { assumption. }
Qed.

Lemma implied_negated_condition: forall ast1 ast2 ast3,
  equiv_typed_smt_expr
    (TypedSMTExpr Sort_BV1 (TypedAST_BinOp Sort_BV1 SMT_And ast1 ast2))
    (TypedSMTExpr Sort_BV1 ast3) ->
  unsat ast3 ->
  equiv_typed_smt_expr
    (TypedSMTExpr Sort_BV1 (TypedAST_BinOp Sort_BV1 SMT_And ast1 (TypedAST_Not Sort_BV1 ast2)))
    (TypedSMTExpr Sort_BV1 ast1).
Proof.
Admitted.
