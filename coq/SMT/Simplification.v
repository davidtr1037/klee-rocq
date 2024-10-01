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

(* TODO: ... *)
Definition normalize_binop_bv1 op (ast1 ast2 : smt_ast Sort_BV1) :=
  AST_BinOp Sort_BV1 op ast1 ast2
.

(* TODO: ... *)
Definition normalize_binop_bv8 op (ast1 ast2 : smt_ast Sort_BV8) :=
  AST_BinOp Sort_BV8 op ast1 ast2
.

(* TODO: ... *)
Definition normalize_binop_bv16 op (ast1 ast2 : smt_ast Sort_BV16) :=
  AST_BinOp Sort_BV16 op ast1 ast2
.

Definition normalize_binop_bv32 op (ast1 ast2 : smt_ast Sort_BV32) :=
  match op with
  | SMT_Add =>
    match ast2 with
    | AST_Const Sort_BV32 n2 =>
        match ast1 with
        | AST_Const Sort_BV32 n1 => AST_BinOp Sort_BV32 op ast1 ast2
        | AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n1) ast =>
            AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 (add n1 n2)) ast
        | _ =>
            AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n2) ast1
        end
    | _ => AST_BinOp Sort_BV32 op ast1 ast2
    end
  (* TOOD: rewrite as above *)
  | SMT_Sub =>
    match ast1, ast2 with
    | AST_Const Sort_BV32 n1, AST_Const Sort_BV32 n2 =>
        AST_BinOp Sort_BV32 op ast1 ast2
    | ast1, AST_Const Sort_BV32 n2 =>
        match ast1 with
        | AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n1) ast =>
            (* (c1 + x) - c2 ~ (c1 - c2) + x *)
            AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 (repr (unsigned (sub n1 n2)))) ast
        | _ =>
            (* (x - c1) ~ ((-c1) + x) *)
            AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 (repr (unsigned (sub zero n2)))) ast1
        end
    | _, _ =>
        AST_BinOp Sort_BV32 op ast1 ast2
    end
  | _ =>
    AST_BinOp Sort_BV32 op ast1 ast2
  end
.

(* TODO: ... *)
Definition normalize_binop_bv64 op (ast1 ast2 : smt_ast Sort_BV64) :=
  AST_BinOp Sort_BV64 op ast1 ast2
.

Definition normalize_binop op (s : smt_sort) (ast1 ast2 : smt_ast s) : smt_ast s :=
  let f :=
    match s with
    | Sort_BV1 => normalize_binop_bv1
    | Sort_BV8 => normalize_binop_bv8
    | Sort_BV16 => normalize_binop_bv16
    | Sort_BV32 => normalize_binop_bv32
    | Sort_BV64 => normalize_binop_bv64
    end in
  f op ast1 ast2
.

Definition normalize_cmpop op (s : smt_sort) (ast1 ast2 : smt_ast s) : smt_ast Sort_BV1 :=
  match op with
  | SMT_Sge => AST_CmpOp s SMT_Sle ast2 ast1
  | SMT_Sgt => AST_CmpOp s SMT_Slt ast2 ast1
  | SMT_Uge => AST_CmpOp s SMT_Ule ast2 ast1
  | SMT_Ugt => AST_CmpOp s SMT_Ult ast2 ast1
  | SMT_Ne =>
      AST_CmpOp Sort_BV1 SMT_Eq (AST_Const Sort_BV1 zero) (AST_CmpOp s SMT_Eq ast1 ast2)
  | _ => AST_CmpOp s op ast1 ast2
  end
.

Definition normalize_not (s : smt_sort) (ast : smt_ast s) : smt_ast s :=
  let f :=
    match s with
    | Sort_BV1 =>
        AST_CmpOp Sort_BV1 SMT_Eq smt_ast_false
    | Sort_BV8 => AST_Not Sort_BV8
    | Sort_BV16 => AST_Not Sort_BV16
    | Sort_BV32 => AST_Not Sort_BV32
    | Sort_BV64 => AST_Not Sort_BV64
    end in
  f ast
.

Fixpoint normalize (s : smt_sort) (ast : smt_ast s) : smt_ast s :=
  match ast with
  | AST_Const sort n => AST_Const sort n
  | AST_Var sort x => AST_Var sort x
  | AST_BinOp sort op ast1 ast2 =>
      normalize_binop op sort (normalize sort ast1) (normalize sort ast2)
  | AST_CmpOp sort op ast1 ast2 =>
      normalize_cmpop op sort (normalize sort ast1) (normalize sort ast2)
  | AST_Not sort ast =>
      normalize_not sort (normalize sort ast)
  end
.

Definition simplify_binop_bv1 op (ast1 ast2 : smt_ast Sort_BV1) :=
  match ast1, ast2 with
  | AST_Const Sort_BV1 n1, AST_Const Sort_BV1 n2 =>
      match op with
      | SMT_Add => AST_Const Sort_BV1 (add n1 n2)
      | SMT_Sub => AST_Const Sort_BV1 (sub n1 n2)
      | SMT_Mul => AST_Const Sort_BV1 (mul n1 n2)
      | SMT_And => AST_Const Sort_BV1 (and n1 n2)
      | _ => AST_BinOp Sort_BV1 op ast1 ast2
      end
  | AST_Const Sort_BV1 n1, ast2 =>
      match op with
      | SMT_And => if eq n1 zero then smt_ast_false else ast2
      | _ => AST_BinOp Sort_BV1 op ast1 ast2
      end
  | ast1, AST_Const Sort_BV1 n2 =>
      match op with
      | SMT_And => if eq n2 zero then smt_ast_false else ast1
      | _ => AST_BinOp Sort_BV1 op ast1 ast2
      end
  | _, _ => AST_BinOp Sort_BV1 op ast1 ast2
  end
.

Definition simplify_binop_bv8 op (ast1 ast2 : smt_ast Sort_BV8) :=
  match ast1, ast2 with
  | AST_Const Sort_BV8 n1, AST_Const Sort_BV8 n2 =>
      match op with
      | SMT_Add => AST_Const Sort_BV8 (add n1 n2)
      | SMT_Sub => AST_Const Sort_BV8 (sub n1 n2)
      | SMT_Mul => AST_Const Sort_BV8 (mul n1 n2)
      | _ => AST_BinOp Sort_BV8 op ast1 ast2
      end
  | _, _ => AST_BinOp Sort_BV8 op ast1 ast2
  end
.

Definition simplify_binop_bv16 op (ast1 ast2 : smt_ast Sort_BV16) :=
  match ast1, ast2 with
  | AST_Const Sort_BV16 n1, AST_Const Sort_BV16 n2 =>
      match op with
      | SMT_Add => AST_Const Sort_BV16 (add n1 n2)
      | SMT_Sub => AST_Const Sort_BV16 (sub n1 n2)
      | SMT_Mul => AST_Const Sort_BV16 (mul n1 n2)
      | _ => AST_BinOp Sort_BV16 op ast1 ast2
      end
  | _, _ => AST_BinOp Sort_BV16 op ast1 ast2
  end
.

Definition simplify_binop_bv32 op (ast1 ast2 : smt_ast Sort_BV32) :=
  match ast1, ast2 with
  | AST_Const Sort_BV32 n1, AST_Const Sort_BV32 n2 =>
      match op with
      | SMT_Add => AST_Const Sort_BV32 (add n1 n2)
      | SMT_Sub => AST_Const Sort_BV32 (sub n1 n2)
      | SMT_Mul => AST_Const Sort_BV32 (mul n1 n2)
      | _ => AST_BinOp Sort_BV32 op ast1 ast2
      end
  | AST_Const Sort_BV32 n1, ast =>
      match op with
      | SMT_Add =>
          if (eq n1 zero) then
            ast
          else
            AST_BinOp Sort_BV32 op ast1 ast2
      | _ => AST_BinOp Sort_BV32 op ast1 ast2
      end
  | _, _ => AST_BinOp Sort_BV32 op ast1 ast2
  end
.

Definition simplify_binop_bv64 op (ast1 ast2 : smt_ast Sort_BV64) :=
  match ast1, ast2 with
  | AST_Const Sort_BV64 n1, AST_Const Sort_BV64 n2 =>
      match op with
      | SMT_Add => AST_Const Sort_BV64 (add n1 n2)
      | SMT_Sub => AST_Const Sort_BV64 (sub n1 n2)
      | SMT_Mul => AST_Const Sort_BV64 (mul n1 n2)
      | _ => AST_BinOp Sort_BV64 op ast1 ast2
      end
  | _, _ => AST_BinOp Sort_BV64 op ast1 ast2
  end
.

Definition simplify_binop op (s : smt_sort) (ast1 ast2 : smt_ast s) : smt_ast s :=
  let f :=
    match s with
    | Sort_BV1 => simplify_binop_bv1
    | Sort_BV8 => simplify_binop_bv8
    | Sort_BV16 => simplify_binop_bv16
    | Sort_BV32 => simplify_binop_bv32
    | Sort_BV64 => simplify_binop_bv64
    end in
  f op ast1 ast2
.

Definition simplify_cmpop_bv1 op (ast1 ast2 : smt_ast Sort_BV1) :=
  match ast1, ast2 with
  | AST_Const Sort_BV1 n1, AST_Const Sort_BV1 n2 =>
      match op with
      | SMT_Eq => (make_smt_ast_bool (eq n1 n2))
      | SMT_Slt
      | SMT_Sle => make_smt_ast_bool (cmp (smt_cmpop_to_comparison op) n1 n2)
      | SMT_Ult
      | SMT_Ule => make_smt_ast_bool (cmpu (smt_cmpop_to_comparison op) n1 n2)
      | _ => AST_CmpOp Sort_BV1 op ast1 ast2
      end
  | AST_Const Sort_BV1 n1, AST_CmpOp Sort_BV1 SMT_Eq (AST_Const Sort_BV1 n2) ast =>
      match op with
      | SMT_Eq =>
          if andb (eq n1 zero) (eq n2 zero) then
            (* (eq 0 (eq 0 a)) ~ a *)
            ast
          else
            AST_CmpOp Sort_BV1 op ast1 ast2
      | _ => AST_CmpOp Sort_BV1 op ast1 ast2
      end
    | _, _ => AST_CmpOp Sort_BV1 op ast1 ast2
  end
.

Definition simplify_cmpop_bv8 op (ast1 ast2 : smt_ast Sort_BV8) :=
  match ast1, ast2 with
  | AST_Const Sort_BV8 n1, AST_Const Sort_BV8 n2 =>
      match op with
      | SMT_Eq => (make_smt_ast_bool (eq n1 n2))
      | SMT_Slt
      | SMT_Sle => make_smt_ast_bool (cmp (smt_cmpop_to_comparison op) n1 n2)
      | SMT_Ult
      | SMT_Ule => make_smt_ast_bool (cmpu (smt_cmpop_to_comparison op) n1 n2)
      | _ => AST_CmpOp Sort_BV8 op ast1 ast2
      end
  | _, _ => AST_CmpOp Sort_BV8 op ast1 ast2
  end
.

Definition simplify_cmpop_bv16 op (ast1 ast2 : smt_ast Sort_BV16) :=
  match ast1, ast2 with
  | AST_Const Sort_BV16 n1, AST_Const Sort_BV16 n2 =>
      match op with
      | SMT_Eq => (make_smt_ast_bool (eq n1 n2))
      | SMT_Slt
      | SMT_Sle => make_smt_ast_bool (cmp (smt_cmpop_to_comparison op) n1 n2)
      | SMT_Ult
      | SMT_Ule => make_smt_ast_bool (cmpu (smt_cmpop_to_comparison op) n1 n2)
      | _ => AST_CmpOp Sort_BV16 op ast1 ast2
      end
  | _, _ => AST_CmpOp Sort_BV16 op ast1 ast2
  end
.

Definition simplify_cmpop_bv32 op (ast1 ast2 : smt_ast Sort_BV32) :=
  match ast1, ast2 with
  | AST_Const Sort_BV32 n1, AST_Const Sort_BV32 n2 =>
      match op with
      | SMT_Eq => (make_smt_ast_bool (eq n1 n2))
      | SMT_Slt
      | SMT_Sle => make_smt_ast_bool (cmp (smt_cmpop_to_comparison op) n1 n2)
      | SMT_Ult
      | SMT_Ule => make_smt_ast_bool (cmpu (smt_cmpop_to_comparison op) n1 n2)
      | _ => AST_CmpOp Sort_BV32 op ast1 ast2
      end
  | _, _ => AST_CmpOp Sort_BV32 op ast1 ast2
  end
.

Definition simplify_cmpop_bv64 op (ast1 ast2 : smt_ast Sort_BV64) :=
  match ast1, ast2 with
  | AST_Const Sort_BV64 n1, AST_Const Sort_BV64 n2 =>
      match op with
      | SMT_Eq => (make_smt_ast_bool (eq n1 n2))
      | SMT_Slt
      | SMT_Sle => make_smt_ast_bool (cmp (smt_cmpop_to_comparison op) n1 n2)
      | SMT_Ult
      | SMT_Ule => make_smt_ast_bool (cmpu (smt_cmpop_to_comparison op) n1 n2)
      | _ => AST_CmpOp Sort_BV64 op ast1 ast2
      end
  | _, _ => AST_CmpOp Sort_BV64 op ast1 ast2
  end
.

Definition simplify_cmpop op (s : smt_sort) (ast1 ast2 : smt_ast s) : smt_ast Sort_BV1 :=
  let f :=
    match s with
    | Sort_BV1 => simplify_cmpop_bv1
    | Sort_BV8 => simplify_cmpop_bv8
    | Sort_BV16 => simplify_cmpop_bv16
    | Sort_BV32 => simplify_cmpop_bv32
    | Sort_BV64 => simplify_cmpop_bv64
    end in
  f op ast1 ast2
.

Fixpoint simplify (s : smt_sort) (ast : smt_ast s) : smt_ast s :=
  match ast with
  | AST_Const sort n => AST_Const sort n
  | AST_Var sort x => AST_Var sort x
  | AST_BinOp sort op ast1 ast2 =>
      simplify_binop op sort (simplify sort ast1) (simplify sort ast2)
  | AST_CmpOp sort op ast1 ast2 =>
      simplify_cmpop op sort (simplify sort ast1) (simplify sort ast2)
  | AST_Not sort ast => AST_Not sort (simplify sort ast)
  end
.

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

Lemma L_4 : forall n1 n2 n3 n4,
  equiv_smt_expr
    (Expr Sort_BV32 (AST_Const Sort_BV32 n1))
    (Expr Sort_BV32 (AST_Const Sort_BV32 n2)) ->
  equiv_smt_expr
    (Expr Sort_BV32 (AST_Const Sort_BV32 n3))
    (Expr Sort_BV32 (AST_Const Sort_BV32 n4)) ->
  equiv_smt_expr (Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.add n1 n3)))
    (Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.add n2 n4))).
Proof.
Admitted.

(*
  all the cases:
   - (normalize (a1 + a2) c), (normalize (a1 + a2) a3)
  where (normalize (a1 + a2) a3) does nothing
*)
Lemma L_3 : forall ast1 ast2 ast3 n,
  (normalize_binop_bv32
    SMT_Add
    (AST_BinOp Sort_BV32 SMT_Add ast1 ast2)
    (AST_Const Sort_BV32 n)) =
  (AST_BinOp
    Sort_BV32
    SMT_Add
    (AST_Const Sort_BV32 n)
    (AST_BinOp Sort_BV32 SMT_Add ast1 ast2)) ->
  equiv_smt_expr (Expr Sort_BV32 (AST_Const Sort_BV32 n)) (Expr Sort_BV32 ast3) ->
  equiv_smt_expr
    (Expr Sort_BV32
       (normalize_binop_bv32 SMT_Add (AST_BinOp Sort_BV32 SMT_Add ast1 ast2)
          (AST_Const Sort_BV32 n)))
    (Expr Sort_BV32
       (AST_BinOp Sort_BV32 SMT_Add (AST_BinOp Sort_BV32 SMT_Add ast1 ast2)
          ast3)).
Proof.
  intros ast1 ast2 ast3 n Heq Hequiv.
  rewrite Heq.
  eapply equiv_smt_expr_transitivity.
  { apply equiv_smt_expr_add_comm. }
  {
    apply equiv_smt_expr_binop.
    { apply equiv_smt_expr_refl. }
    { assumption. }
  }
Qed.

(*
  all the cases:
  - (normalize a1 c) ~ (normalize a1 a2)
  where (normalize a1 a2) does nothing
*)
Lemma L_2 : forall n ast1 ast2,
  (normalize_binop_bv32 SMT_Add ast1 ast2) = AST_BinOp Sort_BV32 SMT_Add ast1 ast2 ->
  equiv_smt_expr (Expr Sort_BV32 (AST_Const Sort_BV32 n)) (Expr Sort_BV32 ast2) ->
  equiv_smt_expr
    (Expr Sort_BV32 (normalize_binop_bv32 SMT_Add ast1 (AST_Const Sort_BV32 n)))
    (Expr Sort_BV32 (normalize_binop_bv32 SMT_Add ast1 ast2)).
Proof.
  intros n ast1 ast2 Heq Hequiv.
  rewrite Heq.
  dependent destruction ast1;
  (* var, not *)
  try (
    eapply equiv_smt_expr_transitivity;
    [
      apply equiv_smt_expr_add_comm |
      apply equiv_smt_expr_binop;
      [ apply equiv_smt_expr_refl | assumption ]
    ]
  ).
  {
    simpl.
    apply equiv_smt_expr_binop.
    { apply equiv_smt_expr_refl. }
    { assumption. }
  }
  {
    destruct op;
    try (
      simpl;
      eapply equiv_smt_expr_transitivity;
      [
        apply equiv_smt_expr_add_comm |
        (
          apply equiv_smt_expr_binop;
          [
            apply equiv_smt_expr_refl |
            assumption
          ]
        )
      ]
    ).
    (* normalize (a1 + a2) c ~ (a1 + a2) + a3 *)
    {
      remember ast1_1 as a1_1.
      dependent destruction ast1_1;
      (* a1 : !const *)
      try (
        apply L_3;
        [
          rewrite Heqa1_1; simpl; reflexivity |
          assumption
        ]
      ).
      (* normalize (c1 + a1) c2 ~ (c1 + a1) + a2 *)
      {
        rewrite Heqa1_1.
        simpl.
        apply equiv_smt_expr_transitivity with
          (e2 :=
            (Expr Sort_BV32
              (AST_BinOp Sort_BV32 SMT_Add
                (AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n0) ast1_2)
                (AST_Const Sort_BV32 n)))).
        {
          apply equiv_smt_expr_symmetry.
          apply equiv_smt_expr_add_consts.
        }
        {
          apply equiv_smt_expr_binop.
          { apply equiv_smt_expr_refl. }
          { assumption. }
        }
      }
    }
  }
Qed.

(*
  all the cases:
  - (normalize a1 a2) ~ (normalize a1 a3)
  where (normalize a1 a2) does nothing
*)
Lemma L_1 : forall ast1 ast2 ast3,
  (normalize_binop_bv32 SMT_Add ast1 ast2) = AST_BinOp Sort_BV32 SMT_Add ast1 ast2 ->
  equiv_smt_expr (Expr Sort_BV32 ast2) (Expr Sort_BV32 ast3) ->
  equiv_smt_expr
    (Expr Sort_BV32 (normalize_binop_bv32 SMT_Add ast1 ast2))
    (Expr Sort_BV32 (normalize_binop_bv32 SMT_Add ast1 ast3)).
Proof.
  intros ast1 ast2 ast3 Heq Hequiv.
  dependent destruction ast3;
  (* ast3 : !const *)
  try (
    rewrite Heq in *;
    simpl;
    apply equiv_smt_expr_binop;
    [
      apply equiv_smt_expr_refl |
      assumption
    ]
  ).
  (* ast3 : const *)
  {
    apply equiv_smt_expr_symmetry.
    apply L_2.
    { assumption. }
    { apply equiv_smt_expr_symmetry. assumption. }
  }
Qed.

Lemma equiv_smt_expr_normalize_binop_right : forall s op (ast1 ast2 ast3 : smt_ast s),
  equiv_smt_expr (Expr s ast2) (Expr s ast3) ->
  equiv_smt_expr
    (Expr s (normalize_binop op s ast1 ast2))
    (Expr s (normalize_binop op s ast1 ast3)).
Proof.
  intros s op ast1 ast2 ast3 Heq.
  destruct s;
  (* bv1, bv8, bv16, bv64 *)
  try (
    apply equiv_smt_expr_binop;
    try (apply equiv_smt_expr_refl);
    try (assumption)
  ).
  simpl.
  destruct op;
  (* all ops except for add/sub *)
  try (
    apply equiv_smt_expr_binop;
    try (apply equiv_smt_expr_refl);
    try (assumption)
  ).
  {
    dependent destruction ast2;
    (* ast2 : !const *)
    try (
      apply L_1;
      [
        reflexivity |
        assumption
      ]
    ).
    (* ast2 : const *)
    {
      dependent destruction ast3;
      try (
        apply L_2;
        [
          reflexivity |
          assumption
        ]
      ).
      (* ast3 : const *)
      {
        dependent destruction ast1;
        try (
          apply equiv_smt_expr_binop;
          try (apply equiv_smt_expr_refl);
          try (assumption)
        ).
        destruct op;
        (* op : !add *)
        try (
          apply equiv_smt_expr_binop;
          try (apply equiv_smt_expr_refl);
          try (assumption)
        ).
        (* op : add *)
        {
          dependent destruction ast1_1;
          try (
            apply equiv_smt_expr_binop;
            [ assumption | apply equiv_smt_expr_refl ]
          ).
          {
            simpl.
            apply equiv_smt_expr_binop.
            {
              apply L_4.
              { apply equiv_smt_expr_refl. }
              { assumption. }
            }
            { apply equiv_smt_expr_refl. }
          }
        }
      }
    }
  }
  { admit. } (* sub *)
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
