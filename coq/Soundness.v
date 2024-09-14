From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import Symbolic.
From SE Require Import Relation.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

From SE.Utils Require Import IDMap.

Lemma soundness_single_step :
  forall s s' c m,
    sym_step s s' ->
    over_approx_via s c m ->
    sat_sym_state m s' ->
    (exists c', step c c' /\ over_approx_via s' c' m).
Proof.
Admitted.

Lemma soundness :
  forall (mdl : llvm_module) (fid : function_id) (s : sym_state) (m : smt_model),
    exists init_s,
      (init_sym_state mdl fid) = Some init_s ->
      multi_sym_step init_s s ->
      sat_sym_state m s ->
      (exists init_c c, (init_state mdl fid) = Some init_c /\ (multi_step c c) /\ over_approx_via s c m).
Proof.
Admitted.
