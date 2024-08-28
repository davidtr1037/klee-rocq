From Coq Require Import List.

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

Lemma LAUX_1 : forall s v se1 se2 se3,
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
