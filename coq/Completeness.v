From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

Lemma completeness_single_step :
  forall c c' s,
    step c c' -> well_defined s -> over_approx s c -> (exists s', sym_step s s' /\ over_approx s' c').
Proof.
Admitted.

Lemma completeness :
  forall (mdl : llvm_module) (d : llvm_definition) (c : state),
    exists init_c,
      (init_state mdl d) = Some init_c ->
      multi_step init_c c ->
      (exists init_s s, (init_sym_state mdl d) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c).
Proof.
Admitted.
