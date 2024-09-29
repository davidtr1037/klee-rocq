From Coq Require Import Logic.Eqdep.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Require Import Coq.Program.Equality.

From SE Require Import BitVectors.
From SE Require Import DynamicValue.

From SE.Numeric Require Import Integers.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

From SE.Utils Require Import StringMap.

Lemma equiv_smt_expr_add_comm : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr s (AST_BinOp s SMT_Add ast1 ast2))
    (Expr s (AST_BinOp s SMT_Add ast2 ast1)).
Proof.
Admitted.

(* TODO: make generic *)
Lemma equiv_smt_expr_sub_add : forall (n : int32) (ast : smt_ast Sort_BV32),
  equiv_smt_expr
    (Expr Sort_BV32 (AST_BinOp Sort_BV32 SMT_Sub ast (AST_Const Sort_BV32 n)))
    (Expr
      Sort_BV32
      (AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 (repr (unsigned (sub zero n)))) ast)).
Proof.
Admitted.

(* TODO: make generic *)
Lemma equiv_smt_expr_add_consts : forall (ast : smt_ast Sort_BV32) (n1 n2 : int32),
  equiv_smt_expr
    (Expr Sort_BV32
       (AST_BinOp Sort_BV32 SMT_Add
          (AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n1) ast)
          (AST_Const Sort_BV32 n2)))
    (Expr Sort_BV32
       (AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 (Int32.add n1 n2)) ast)).
Proof.
Admitted.

(* TODO: make generic *)
Lemma equiv_smt_expr_sub_consts : forall (ast : smt_ast Sort_BV32) (n1 n2 : int32),
  equiv_smt_expr
    (Expr Sort_BV32
       (AST_BinOp Sort_BV32 SMT_Sub
          (AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n1) ast)
          (AST_Const Sort_BV32 n2)))
    (Expr Sort_BV32
       (AST_BinOp Sort_BV32 SMT_Add
          (AST_Const Sort_BV32 (Int32.repr (Int32.unsigned (Int32.sub n1 n2))))
          ast)).
Proof.
Admitted.

Lemma equiv_smt_expr_normalize_binop : forall s op (ast1 ast2 ast3 ast4 : smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s ast2) ->
  equiv_smt_expr (Expr s ast3) (Expr s ast4) ->
  equiv_smt_expr
    (Expr s (normalize_binop op s ast1 ast3))
    (Expr s (normalize_binop op s ast2 ast4)).
Proof.
  intros s op ast1 ast2 ast3 ast4 Heq1 Heq2.
  destruct s; destruct op;
  try (apply equiv_smt_expr_binop; assumption).
  {
    dependent destruction ast1;
    dependent destruction ast2;
    dependent destruction ast3;
    dependent destruction ast4;
    try (apply equiv_smt_expr_binop; assumption);
    try (
      simpl;
      eapply equiv_smt_expr_transitivity;
      (try eapply equiv_smt_expr_add_comm);
      (try apply equiv_smt_expr_binop; assumption)
    ).
    {
      destruct op;
      try (
        eapply equiv_smt_expr_transitivity;
        try (eapply equiv_smt_expr_add_comm);
        try (apply equiv_smt_expr_binop; assumption)
      ).
      dependent destruction ast2_1;
      (* no change *)
      try (apply equiv_smt_expr_binop; assumption).
      {
        simpl.
        eapply equiv_smt_expr_transitivity.
        { apply equiv_smt_expr_binop; eassumption. }
        {
          eapply equiv_smt_expr_transitivity.
          { eapply equiv_smt_expr_add_comm. }
          { apply equiv_smt_expr_add_consts. }
        }
      }
    }
Admitted.

Lemma equiv_smt_expr_normalize_binop_args : forall s op (ast1 ast2 : smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s (normalize s ast1)) ->
  equiv_smt_expr (Expr s ast2) (Expr s (normalize s ast2)) ->
  equiv_smt_expr
    (Expr s (AST_BinOp s op ast1 ast2))
    (Expr
       s
       (normalize_binop op s ast1 ast2)) ->
  equiv_smt_expr
    (Expr s (AST_BinOp s op ast1 ast2))
    (Expr
       s
       (normalize_binop op s (normalize s ast1) (normalize s ast2))).
Proof.
  intros s op ast1 ast2 H1 H2 H3.
  apply equiv_smt_expr_transitivity with
    (e2 := (Expr s (normalize_binop op s ast1 ast2))).
  { assumption. }
  { apply equiv_smt_expr_normalize_binop; assumption. }
Qed.

Lemma equiv_smt_expr_normalize_cmpop : forall s op (ast1 ast2 ast3 ast4 : smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s ast2) ->
  equiv_smt_expr (Expr s ast3) (Expr s ast4) ->
  equiv_smt_expr
    (Expr Sort_BV1 (normalize_cmpop op s ast1 ast3))
    (Expr Sort_BV1 (normalize_cmpop op s ast2 ast4)).
Proof.
  intros s op ast1 ast2 ast3 ast4 Heq1 Heq2.
  destruct s; destruct op;
  (* simpl case *)
  try (
    simpl;
    apply equiv_smt_expr_cmpop; assumption
  );
  (* Ne --> Eq 0 ... *)
  try (
    simpl;
    apply equiv_smt_expr_cmpop;
    try (apply equiv_smt_expr_refl);
    try (apply equiv_smt_expr_cmpop; assumption)
  ).
Qed.

Lemma equiv_smt_expr_normalize_cmpop_args : forall s op (ast1 ast2 : smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s (normalize s ast1)) ->
  equiv_smt_expr (Expr s ast2) (Expr s (normalize s ast2)) ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s op ast1 ast2))
    (Expr Sort_BV1 (normalize_cmpop op s ast1 ast2)) ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s op ast1 ast2))
    (Expr Sort_BV1 (normalize_cmpop op s (normalize s ast1) (normalize s ast2))).
Proof.
  intros s op ast1 ast2 H1 H2 H3.
  apply equiv_smt_expr_transitivity with
    (e2 := (Expr Sort_BV1 (normalize_cmpop op s ast1 ast2))).
  { assumption. }
  { apply equiv_smt_expr_normalize_cmpop; assumption. }
Qed.

Lemma equiv_smt_expr_ugt_ult : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Ugt ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Ult ast2 ast1)).
Proof.
Admitted.

Lemma equiv_smt_expr_uge_ule : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Uge ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Ule ast2 ast1)).
Proof.
Admitted.

Lemma equiv_smt_expr_sgt_slt : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Sgt ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Slt ast2 ast1)).
Proof.
Admitted.

Lemma equiv_smt_expr_sge_sle : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Sge ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Sle ast2 ast1)).
Proof.
Admitted.

Lemma equiv_smt_expr_not_to_eq : forall (ast : smt_ast Sort_BV1),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_Not Sort_BV1 ast))
    (Expr Sort_BV1 (AST_CmpOp Sort_BV1 SMT_Eq smt_ast_false (normalize Sort_BV1 ast))).
Proof.
Admitted.

Lemma equiv_smt_expr_ne_to_eq : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr (Expr Sort_BV1 (AST_CmpOp s SMT_Ne ast1 ast2))
    (Expr Sort_BV1
       (AST_CmpOp Sort_BV1 SMT_Eq (AST_Const Sort_BV1 Int1.zero)
          (AST_CmpOp s SMT_Eq ast1 ast2))).
Proof.
Admitted.

Lemma equiv_smt_expr_normalize: forall (sort : smt_sort) (ast : smt_ast sort),
  equiv_smt_expr
    (Expr sort ast)
    (Expr sort (normalize sort ast)).
Proof.
  intros sort ast.
  induction ast; simpl.
  { apply equiv_smt_expr_refl. }
  { apply equiv_smt_expr_refl. }
  {
    destruct s.
    {
      simpl.
      unfold normalize_binop_bv1.
      apply equiv_smt_expr_binop with (ast1 := ast1) (ast3 := ast2); assumption.
    }
    {
      simpl.
      unfold normalize_binop_bv8.
      apply equiv_smt_expr_binop with (ast1 := ast1) (ast3 := ast2); assumption.
    }
    {
      simpl.
      unfold normalize_binop_bv16.
      apply equiv_smt_expr_binop with (ast1 := ast1) (ast3 := ast2); assumption.
    }
    {
      dependent destruction ast1; dependent destruction ast2; destruct op;
      (* trivial cases *)
      try (
        apply equiv_smt_expr_normalize_binop_args;
        try assumption;
        apply equiv_smt_expr_refl
      );
      try (
        apply equiv_smt_expr_normalize_binop_args;
        try assumption;
        apply equiv_smt_expr_add_comm
      );
      try (
        apply equiv_smt_expr_normalize_binop_args;
        try assumption;
        apply equiv_smt_expr_sub_add
      ).
      {
        apply equiv_smt_expr_normalize_binop_args.
        { assumption. }
        { assumption. }
        {
          destruct op0;
          try apply equiv_smt_expr_add_comm.
          dependent destruction ast1_1;
          try apply equiv_smt_expr_add_comm.
          simpl.
          apply equiv_smt_expr_add_consts.
        }
      }
      {
        apply equiv_smt_expr_normalize_binop_args.
        { assumption. }
        { assumption. }
        {
          destruct op0;
          try apply equiv_smt_expr_sub_add.
          dependent destruction ast1_1;
          try apply equiv_smt_expr_sub_add.
          simpl.
          apply equiv_smt_expr_sub_consts.
        }
      }
    }
    {
      apply equiv_smt_expr_binop with (ast1 := ast1) (ast3 := ast2); assumption.
    }
  }
  {
    destruct op;
    try (
      apply equiv_smt_expr_normalize_cmpop_args;
      try assumption;
      apply equiv_smt_expr_refl
    ).
    {
      apply equiv_smt_expr_normalize_cmpop_args;
      try assumption.
      simpl.
      apply equiv_smt_expr_ne_to_eq.
    }
    {
      apply equiv_smt_expr_normalize_cmpop_args;
      try assumption.
      simpl.
      apply equiv_smt_expr_ugt_ult.
    }
    {
      apply equiv_smt_expr_normalize_cmpop_args;
      try assumption.
      simpl.
      apply equiv_smt_expr_uge_ule.
    }
    {
      apply equiv_smt_expr_normalize_cmpop_args;
      try assumption.
      simpl.
      apply equiv_smt_expr_sgt_slt.
    }
    {
      apply equiv_smt_expr_normalize_cmpop_args;
      try assumption.
      simpl.
      apply equiv_smt_expr_sge_sle.
    }
  }
  {
    destruct s;
    try (
      simpl;
      apply equiv_smt_expr_not;
      assumption
    ).
    apply equiv_smt_expr_not_to_eq.
  }
Qed.

Lemma equiv_smt_expr_normalize_simplify: forall (sort : smt_sort) (ast : smt_ast sort),
  equiv_smt_expr
    (Expr sort ast)
    (Expr sort (simplify sort (normalize sort ast))).
Proof.
Admitted.
