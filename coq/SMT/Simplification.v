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
  | SMT_Sub =>
    match ast2 with
    | AST_Const Sort_BV32 n2 =>
        match ast1 with
        | AST_Const Sort_BV32 n1 => AST_BinOp Sort_BV32 op ast1 ast2
        | AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n1) ast =>
            AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 (repr (unsigned (sub n1 n2)))) ast
        | _ =>
            AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 (repr (unsigned (sub zero n2)))) ast1
        end
    | _ => AST_BinOp Sort_BV32 op ast1 ast2
    end
  | SMT_Mul =>
    match ast2 with
    | AST_Const Sort_BV32 n2 =>
        match ast1 with
        | AST_Const Sort_BV32 n1 => AST_BinOp Sort_BV32 op ast1 ast2
        | _ => AST_BinOp Sort_BV32 SMT_Mul (AST_Const Sort_BV32 n2) ast1
        end
    | _ => AST_BinOp Sort_BV32 SMT_Mul ast1 ast2
    end
  | SMT_And =>
    match ast1 with
    | AST_Const Sort_BV32 n1 =>
        match ast2 with
        | AST_Const Sort_BV32 n2 => AST_BinOp Sort_BV32 op ast1 ast2
        | _ => AST_BinOp Sort_BV32 SMT_And ast2 (AST_Const Sort_BV32 n1)
        end
    | _ => AST_BinOp Sort_BV32 SMT_And ast1 ast2
    end
  | SMT_Or =>
    match ast1 with
    | AST_Const Sort_BV32 n1 =>
        match ast2 with
        | AST_Const Sort_BV32 n2 => AST_BinOp Sort_BV32 op ast1 ast2
        | _ => AST_BinOp Sort_BV32 SMT_Or ast2 (AST_Const Sort_BV32 n1)
        end
    | _ => AST_BinOp Sort_BV32 SMT_Or ast1 ast2
    end
  | SMT_Xor =>
    match ast2 with
    | AST_Const Sort_BV32 n2 =>
        match ast1 with
        | AST_Const Sort_BV32 n1 => AST_BinOp Sort_BV32 op ast1 ast2
        | _ => AST_BinOp Sort_BV32 SMT_Xor (AST_Const Sort_BV32 n2) ast1
        end
    | _ => AST_BinOp Sort_BV32 SMT_Xor ast1 ast2
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

Definition normalize_cmpop_bv1 op (ast1 ast2 : smt_ast Sort_BV1) : smt_ast Sort_BV1 :=
  match op with
  | SMT_Sge => AST_CmpOp Sort_BV1 SMT_Sle ast2 ast1
  | SMT_Sgt => AST_CmpOp Sort_BV1 SMT_Slt ast2 ast1
  | SMT_Uge => AST_CmpOp Sort_BV1 SMT_Ule ast2 ast1
  | SMT_Ugt => AST_CmpOp Sort_BV1 SMT_Ult ast2 ast1
  | SMT_Eq =>
      match ast2 with
      | AST_Const Sort_BV1 n2 =>
          match ast1 with
          | AST_Const Sort_BV1 n1 => AST_CmpOp Sort_BV1 op ast1 ast2
          | _ => AST_CmpOp Sort_BV1 op (AST_Const Sort_BV1 n2) ast1
          end
      | _ => AST_CmpOp Sort_BV1 op ast1 ast2
      end
  | SMT_Ne =>
      match ast2 with
      | AST_Const Sort_BV1 n2 =>
          AST_CmpOp Sort_BV1 SMT_Eq
            (AST_Const Sort_BV1 zero)
            (AST_CmpOp Sort_BV1 SMT_Eq (AST_Const Sort_BV1 n2) ast1)
      | _ =>
          AST_CmpOp Sort_BV1 SMT_Eq
            (AST_Const Sort_BV1 zero)
            (AST_CmpOp Sort_BV1 SMT_Eq ast1 ast2)
      end
  | _ => AST_CmpOp Sort_BV1 op ast1 ast2
  end
.

Definition normalize_cmpop_bv8 op (ast1 ast2 : smt_ast Sort_BV8) : smt_ast Sort_BV1 :=
  AST_CmpOp Sort_BV8 op ast1 ast2
.

Definition normalize_cmpop_bv16 op (ast1 ast2 : smt_ast Sort_BV16) : smt_ast Sort_BV1 :=
  AST_CmpOp Sort_BV16 op ast1 ast2
.

Definition normalize_cmpop_bv32 op (ast1 ast2 : smt_ast Sort_BV32) : smt_ast Sort_BV1 :=
  match op with
  | SMT_Sge => AST_CmpOp Sort_BV32 SMT_Sle ast2 ast1
  | SMT_Sgt => AST_CmpOp Sort_BV32 SMT_Slt ast2 ast1
  | SMT_Uge => AST_CmpOp Sort_BV32 SMT_Ule ast2 ast1
  | SMT_Ugt => AST_CmpOp Sort_BV32 SMT_Ult ast2 ast1
  | SMT_Eq =>
      match ast2 with
      | AST_Const Sort_BV32 n2 =>
          match ast1 with
          | AST_Const Sort_BV32 n1 => AST_CmpOp Sort_BV32 op ast1 ast2
          | _ => AST_CmpOp Sort_BV32 op (AST_Const Sort_BV32 n2) ast1
          end
      | _ => AST_CmpOp Sort_BV32 op ast1 ast2
      end
  | SMT_Ne =>
      match ast2 with
      | AST_Const Sort_BV32 n2 =>
          AST_CmpOp Sort_BV1 SMT_Eq
            (AST_Const Sort_BV1 zero)
            (AST_CmpOp Sort_BV32 SMT_Eq (AST_Const Sort_BV32 n2) ast1)
      | _ =>
          AST_CmpOp Sort_BV1 SMT_Eq
            (AST_Const Sort_BV1 zero)
            (AST_CmpOp Sort_BV32 SMT_Eq ast1 ast2)
      end
  | _ => AST_CmpOp Sort_BV32 op ast1 ast2
  end
.

Definition normalize_cmpop_bv64 op (ast1 ast2 : smt_ast Sort_BV64) : smt_ast Sort_BV1 :=
  match op with
  | SMT_Sge => AST_CmpOp Sort_BV64 SMT_Sle ast2 ast1
  | SMT_Sgt => AST_CmpOp Sort_BV64 SMT_Slt ast2 ast1
  | SMT_Uge => AST_CmpOp Sort_BV64 SMT_Ule ast2 ast1
  | SMT_Ugt => AST_CmpOp Sort_BV64 SMT_Ult ast2 ast1
  | SMT_Eq =>
      match ast2 with
      | AST_Const Sort_BV64 n2 =>
          match ast1 with
          | AST_Const Sort_BV64 n1 => AST_CmpOp Sort_BV64 op ast1 ast2
          | _ => AST_CmpOp Sort_BV64 op (AST_Const Sort_BV64 n2) ast1
          end
      | _ => AST_CmpOp Sort_BV64 op ast1 ast2
      end
  | SMT_Ne =>
      match ast2 with
      | AST_Const Sort_BV64 n2 =>
          AST_CmpOp Sort_BV1 SMT_Eq
            (AST_Const Sort_BV1 zero)
            (AST_CmpOp Sort_BV64 SMT_Eq (AST_Const Sort_BV64 n2) ast1)
      | _ =>
          AST_CmpOp Sort_BV1 SMT_Eq
            (AST_Const Sort_BV1 zero)
            (AST_CmpOp Sort_BV64 SMT_Eq ast1 ast2)
      end
  | _ => AST_CmpOp Sort_BV64 op ast1 ast2
  end
.

Definition normalize_cmpop op (s : smt_sort) (ast1 ast2 : smt_ast s) : smt_ast Sort_BV1 :=
  let f :=
    match s with
    | Sort_BV1 => normalize_cmpop_bv1
    | Sort_BV8 => normalize_cmpop_bv8
    | Sort_BV16 => normalize_cmpop_bv16
    | Sort_BV32 => normalize_cmpop_bv32
    | Sort_BV64 => normalize_cmpop_bv64
    end in
  f op ast1 ast2
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

Definition normalize_zext (s : smt_sort) (ast : smt_ast s) (cast_sort : smt_sort) : smt_ast cast_sort :=
  AST_ZExt s ast cast_sort
.

Definition normalize_sext (s : smt_sort) (ast : smt_ast s) (cast_sort : smt_sort) : smt_ast cast_sort :=
  AST_SExt s ast cast_sort
.

Definition normalize_extract (s : smt_sort) (ast : smt_ast s) (cast_sort : smt_sort) : smt_ast cast_sort :=
  AST_Extract s ast cast_sort
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
  | AST_ZExt sort ast cast_sort =>
      normalize_zext sort (normalize sort ast) cast_sort
  | AST_SExt sort ast cast_sort =>
      normalize_sext sort (normalize sort ast) cast_sort
  | AST_Extract sort ast cast_sort =>
      normalize_extract sort (normalize sort ast) cast_sort
  | AST_Select sort cond ast1 ast2 => AST_Select sort cond ast1 ast2
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
  AST_BinOp Sort_BV8 op ast1 ast2
.

Definition simplify_binop_bv16 op (ast1 ast2 : smt_ast Sort_BV16) :=
  AST_BinOp Sort_BV16 op ast1 ast2
.

Definition simplify_binop_bv32 op (ast1 ast2 : smt_ast Sort_BV32) :=
  match ast1, ast2 with
  | AST_Const Sort_BV32 n1, AST_Const Sort_BV32 n2 =>
      match op with
      | SMT_Add => AST_Const Sort_BV32 (add n1 n2)
      | SMT_Sub => AST_Const Sort_BV32 (sub n1 n2)
      | SMT_Mul => AST_Const Sort_BV32 (mul n1 n2)
      | SMT_UDiv => AST_Const Sort_BV32 (divu n1 n2)
      | SMT_SDiv => AST_Const Sort_BV32 (divs n1 n2)
      | SMT_URem => AST_Const Sort_BV32 (modu n1 n2)
      | SMT_SRem => AST_Const Sort_BV32 (mods n1 n2)
      | SMT_And => AST_Const Sort_BV32 (and n1 n2)
      | SMT_Or => AST_Const Sort_BV32 (or n1 n2)
      | SMT_Xor => AST_Const Sort_BV32 (xor n1 n2)
      | SMT_Shl => AST_Const Sort_BV32 (shl n1 n2)
      | SMT_LShr => AST_Const Sort_BV32 (shru n1 n2)
      | SMT_AShr => AST_Const Sort_BV32 (shr n1 n2)
      end
  | AST_Const Sort_BV32 n1, ast =>
      match op with
      | SMT_Add =>
          if (eq n1 zero) then
            ast
          else
            AST_BinOp Sort_BV32 op ast1 ast2
      | SMT_Or => if (eq n1 zero) then ast2 else AST_BinOp Sort_BV32 op ast1 ast2
      | _ => AST_BinOp Sort_BV32 op ast1 ast2
      end
  | ast1, AST_Const Sort_BV32 n2 =>
      match op with
      | SMT_Or => if (eq n2 zero) then ast1 else AST_BinOp Sort_BV32 op ast1 ast2
      | _ => AST_BinOp Sort_BV32 op ast1 ast2
      end
  | _, _ => AST_BinOp Sort_BV32 op ast1 ast2
  end
.

Definition simplify_binop_bv64 op (ast1 ast2 : smt_ast Sort_BV64) :=
  AST_BinOp Sort_BV64 op ast1 ast2
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
  AST_CmpOp Sort_BV8 op ast1 ast2
.

Definition simplify_cmpop_bv16 op (ast1 ast2 : smt_ast Sort_BV16) :=
  AST_CmpOp Sort_BV16 op ast1 ast2
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

Definition simplify_zext (s : smt_sort) (ast : smt_ast s) (cast_sort : smt_sort) : smt_ast cast_sort :=
  match ast with
  | AST_Const sort n =>
      AST_Const cast_sort (smt_eval_zext_by_sort sort n cast_sort)
  | _ =>
      AST_ZExt s ast cast_sort
  end
.

Definition simplify_sext (s : smt_sort) (ast : smt_ast s) (cast_sort : smt_sort) : smt_ast cast_sort :=
  match ast with
  | AST_Const sort n =>
      AST_Const cast_sort (smt_eval_sext_by_sort sort n cast_sort)
  | _ =>
      AST_SExt s ast cast_sort
  end
.

Definition simplify_extract (s : smt_sort) (ast : smt_ast s) (cast_sort : smt_sort) : smt_ast cast_sort :=
  match ast with
  | AST_Const sort n =>
      AST_Const cast_sort (smt_eval_extract_by_sort sort n cast_sort)
  | _ =>
      AST_Extract s ast cast_sort
  end
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
  | AST_ZExt sort ast cast_sort =>
      simplify_zext sort (simplify sort ast) cast_sort
  | AST_SExt sort ast cast_sort =>
      simplify_sext sort (simplify sort ast) cast_sort
  | AST_Extract sort ast cast_sort =>
      simplify_extract sort (simplify sort ast) cast_sort
  | AST_Select sort cond ast1 ast2 => AST_Select sort cond ast1 ast2
  end
.

Lemma equiv_smt_expr_add_comm : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr s (AST_BinOp s SMT_Add ast1 ast2))
    (Expr s (AST_BinOp s SMT_Add ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s; simpl.
  { apply Int1.add_commut. }
  { apply Int8.add_commut. }
  { apply Int16.add_commut. }
  { apply Int32.add_commut. }
  { apply Int64.add_commut. }
Qed.

(* TODO: make generic *)
Lemma equiv_smt_expr_sub_add_bv32 : forall (n : int32) (ast : smt_ast Sort_BV32),
  equiv_smt_expr
    (Expr
      Sort_BV32
      (AST_BinOp Sort_BV32 SMT_Sub ast (AST_Const Sort_BV32 n)))
    (Expr
      Sort_BV32
      (AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 (repr (unsigned (sub zero n)))) ast)).
Proof.
  intros n ast.
  apply EquivExpr.
  intros m.
  simpl.
  rewrite Int32.add_commut.
  apply int32_sub_add.
Qed.

(* TODO: finalize? *)
Lemma equiv_smt_expr_add_consts_generic : forall (s : smt_sort) `{VInt (smt_sort_to_int_type s)} (ast : smt_ast s) (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s
       (AST_BinOp s SMT_Add
          (AST_BinOp s SMT_Add (AST_Const s n1) ast)
          (AST_Const s n2)))
    (Expr s (AST_BinOp s SMT_Add (AST_Const s (add n1 n2)) ast)).
Proof.
  intros s H ast n1 n2.
  apply EquivExpr.
  intros m.
  simpl.
  destruct s.
  {
    simpl.
    rewrite (Int1.add_assoc n1 _ n2).
    rewrite (Int1.add_commut _ n2).
    rewrite <- (Int1.add_assoc n1 n2 _).
    admit.
  }
Admitted.

(* TODO: make generic *)
Lemma equiv_smt_expr_add_consts_bv32 : forall (ast : smt_ast Sort_BV32) (n1 n2 : int32),
  equiv_smt_expr
    (Expr Sort_BV32
       (AST_BinOp Sort_BV32 SMT_Add
          (AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n1) ast)
          (AST_Const Sort_BV32 n2)))
    (Expr Sort_BV32
       (AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 (Int32.add n1 n2)) ast)).
Proof.
  intros ast n1 n2.
  apply EquivExpr.
  intros m.
  simpl.
  rewrite (Int32.add_assoc n1 _ n2).
  rewrite (Int32.add_commut _ n2).
  rewrite <- (Int32.add_assoc n1 n2 _).
  reflexivity.
Qed.

(* TODO: make generic *)
Lemma equiv_smt_expr_sub_consts_bv32 : forall (ast : smt_ast Sort_BV32) (n1 n2 : int32),
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
  intros ast n1 n2.
  apply EquivExpr.
  intros m.
  simpl.
  rewrite Int32.sub_add_l.
  rewrite Int32.repr_unsigned.
  reflexivity.
Qed.

Lemma equiv_smt_expr_mul_comm : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr s (AST_BinOp s SMT_Mul ast1 ast2))
    (Expr s (AST_BinOp s SMT_Mul ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s; simpl.
  { apply Int1.mul_commut. }
  { apply Int8.mul_commut. }
  { apply Int16.mul_commut. }
  { apply Int32.mul_commut. }
  { apply Int64.mul_commut. }
Qed.

Lemma equiv_smt_expr_eq_comm : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Eq ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Eq ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s;
  simpl; unfold smt_eval_cmpop_by_sort, smt_eval_cmpop_generic; simpl.
  { rewrite Int1.eq_sym. reflexivity. }
  { rewrite Int8.eq_sym. reflexivity. }
  { rewrite Int16.eq_sym. reflexivity. }
  { rewrite Int32.eq_sym. reflexivity. }
  { rewrite Int64.eq_sym. reflexivity. }
Qed.

Lemma equiv_smt_expr_and_comm : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr s (AST_BinOp s SMT_And ast1 ast2))
    (Expr s (AST_BinOp s SMT_And ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s; simpl.
  { apply Int1.and_commut. }
  { apply Int8.and_commut. }
  { apply Int16.and_commut. }
  { apply Int32.and_commut. }
  { apply Int64.and_commut. }
Qed.

Lemma equiv_smt_expr_or_comm : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr s (AST_BinOp s SMT_Or ast1 ast2))
    (Expr s (AST_BinOp s SMT_Or ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s; simpl.
  { apply Int1.or_commut. }
  { apply Int8.or_commut. }
  { apply Int16.or_commut. }
  { apply Int32.or_commut. }
  { apply Int64.or_commut. }
Qed.

Lemma equiv_smt_expr_xor_comm : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr s (AST_BinOp s SMT_Xor ast1 ast2))
    (Expr s (AST_BinOp s SMT_Xor ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s; simpl.
  { apply Int1.xor_commut. }
  { apply Int8.xor_commut. }
  { apply Int16.xor_commut. }
  { apply Int32.xor_commut. }
  { apply Int64.xor_commut. }
Qed.

Lemma equiv_smt_expr_normalize_binop_bv32 : forall op (ast1 ast2 : smt_ast Sort_BV32),
  equiv_smt_expr
    (Expr Sort_BV32 (normalize_binop_bv32 op ast1 ast2))
    (Expr Sort_BV32 (AST_BinOp Sort_BV32 op ast1 ast2)).
Proof.
  intros op ast1 ast2.
  destruct op;
  try apply equiv_smt_expr_refl.
  (* add *)
  {
    dependent destruction ast2;
    try apply equiv_smt_expr_refl.
    {
      dependent destruction ast1;
      try apply equiv_smt_expr_refl;
      (* not, zext, sext *)
      try (
        simpl;
        eapply equiv_smt_expr_transitivity;
        [ apply equiv_smt_expr_add_comm | apply equiv_smt_expr_refl ]
      ).
      {
        destruct op;
        try (
          eapply equiv_smt_expr_transitivity;
          [ apply equiv_smt_expr_add_comm | apply equiv_smt_expr_refl ]
        ).
        {
          dependent destruction ast1_1;
          try (
            eapply equiv_smt_expr_transitivity;
            [ apply equiv_smt_expr_add_comm | apply equiv_smt_expr_refl ]
          ).
          {
            simpl.
            apply equiv_smt_expr_symmetry.
            apply equiv_smt_expr_add_consts_bv32.
          }
        }
      }
    }
  }
  (* sub *)
  {
    dependent destruction ast2;
    try apply equiv_smt_expr_refl.
    {
      dependent destruction ast1;
      try apply equiv_smt_expr_refl;
      try (
        simpl;
        eapply equiv_smt_expr_transitivity;
        [
          apply equiv_smt_expr_symmetry; apply equiv_smt_expr_sub_add_bv32 |
          apply equiv_smt_expr_refl
        ]
      ).
      {
        destruct op;
        try (
          eapply equiv_smt_expr_transitivity;
          [
            apply equiv_smt_expr_symmetry; apply equiv_smt_expr_sub_add_bv32 |
            apply equiv_smt_expr_refl
          ]
        ).
        {
          dependent destruction ast1_1;
          try (
            eapply equiv_smt_expr_transitivity;
            [
              apply equiv_smt_expr_symmetry; apply equiv_smt_expr_sub_add_bv32 |
              apply equiv_smt_expr_refl
            ]
          ).
          {
            simpl.
            apply equiv_smt_expr_symmetry.
            eapply equiv_smt_expr_transitivity.
            {
              apply equiv_smt_expr_sub_consts_bv32.
            }
            { apply equiv_smt_expr_refl. }
          }
        }
      }
    }
  }
  (* mul *)
  {
    dependent destruction ast2;
    try apply equiv_smt_expr_refl.
    {
      dependent destruction ast1;
      try apply equiv_smt_expr_mul_comm.
      { apply equiv_smt_expr_refl. }
    }
  }
  {
    dependent destruction ast1;
    try apply equiv_smt_expr_refl.
    {
      dependent destruction ast2;
      try apply equiv_smt_expr_and_comm.
      { apply equiv_smt_expr_refl. }
    }
  }
  {
    dependent destruction ast1;
    try apply equiv_smt_expr_refl.
    {
      dependent destruction ast2;
      try apply equiv_smt_expr_or_comm.
      { apply equiv_smt_expr_refl. }
    }
  }
  {
    dependent destruction ast2;
    try apply equiv_smt_expr_refl.
    {
      dependent destruction ast1;
      try apply equiv_smt_expr_xor_comm.
      { apply equiv_smt_expr_refl. }
    }
  }
Qed.

Lemma equiv_smt_expr_normalize_binop : forall s op (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr s (normalize_binop op s ast1 ast2))
    (Expr s (AST_BinOp s op ast1 ast2)).
Proof.
  intros s op ast1 ast2.
  destruct s;
  try apply equiv_smt_expr_refl.
  { apply equiv_smt_expr_normalize_binop_bv32. }
Qed.

Lemma equiv_smt_expr_normalize_binop_args : forall s op (ast1 ast2 : smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s (normalize s ast1)) ->
  equiv_smt_expr (Expr s ast2) (Expr s (normalize s ast2)) ->
  equiv_smt_expr
    (Expr s (AST_BinOp s op ast1 ast2))
    (Expr
       s
       (normalize_binop op s (normalize s ast1) (normalize s ast2))).
Proof.
  intros s op ast1 ast2 H1 H2.
  apply equiv_smt_expr_symmetry.
  eapply equiv_smt_expr_transitivity.
  { apply equiv_smt_expr_normalize_binop. }
  {
    apply equiv_smt_expr_binop;
    apply equiv_smt_expr_symmetry; assumption.
  }
Qed.

Lemma equiv_smt_expr_ne_to_eq : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr (Expr Sort_BV1 (AST_CmpOp s SMT_Ne ast1 ast2))
    (Expr Sort_BV1
       (AST_CmpOp Sort_BV1 SMT_Eq (AST_Const Sort_BV1 Int1.zero)
          (AST_CmpOp s SMT_Eq ast1 ast2))).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  simpl.
  destruct s; unfold smt_eval_cmpop_by_sort; unfold smt_eval_cmpop_generic; simpl.
  {
    remember (Int1.eq (smt_eval_ast m Sort_BV1 ast1) (smt_eval_ast m Sort_BV1 ast2)) as b.
    destruct b; reflexivity.
  }
  {
    remember (Int8.eq (smt_eval_ast m Sort_BV8 ast1) (smt_eval_ast m Sort_BV8 ast2)) as b.
    destruct b; reflexivity.
  }
  {
    remember (Int16.eq (smt_eval_ast m Sort_BV16 ast1) (smt_eval_ast m Sort_BV16 ast2)) as b.
    destruct b; reflexivity.
  }
  {
    remember (Int32.eq (smt_eval_ast m Sort_BV32 ast1) (smt_eval_ast m Sort_BV32 ast2)) as b.
    destruct b; reflexivity.
  }
  {
    remember (Int64.eq (smt_eval_ast m Sort_BV64 ast1) (smt_eval_ast m Sort_BV64 ast2)) as b.
    destruct b; reflexivity.
  }
Qed.

Lemma equiv_smt_expr_ugt_ult : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Ugt ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Ult ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s; reflexivity.
Qed.

Lemma equiv_smt_expr_uge_ule : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Uge ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Ule ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s; reflexivity.
Qed.

Lemma equiv_smt_expr_sgt_slt : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Sgt ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Slt ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s; reflexivity.
Qed.

Lemma equiv_smt_expr_sge_sle : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Sge ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Sle ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  destruct s; reflexivity.
Qed.

(* TODO: make generic *)
Lemma equiv_smt_expr_normalize_cmpop_bv1 : forall op (ast1 ast2 : smt_ast Sort_BV1),
  equiv_smt_expr
    (Expr Sort_BV1 (normalize_cmpop op Sort_BV1 ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp Sort_BV1 op ast1 ast2)).
Proof.
  intros op ast1 ast2.
  destruct op;
  try apply equiv_smt_expr_refl;
  (
    simpl;
    apply equiv_smt_expr_symmetry;
    try apply equiv_smt_expr_ne_to_eq;
    try apply equiv_smt_expr_ugt_ult;
    try apply equiv_smt_expr_uge_ule;
    try apply equiv_smt_expr_sgt_slt;
    try apply equiv_smt_expr_sge_sle
  ).
  {
    dependent destruction ast2;
    try apply equiv_smt_expr_refl.
    {
      dependent destruction ast1;
      try apply equiv_smt_expr_refl;
      try apply equiv_smt_expr_eq_comm.
    }
  }
  {
    dependent destruction ast2;
    try (
      eapply equiv_smt_expr_transitivity;
      [ eapply equiv_smt_expr_ne_to_eq | apply equiv_smt_expr_refl ]
    ).
    {
      eapply equiv_smt_expr_transitivity.
      { eapply equiv_smt_expr_ne_to_eq. }
      {
        apply equiv_smt_expr_cmpop.
        { apply equiv_smt_expr_refl. }
        { apply equiv_smt_expr_eq_comm. }
      }
    }
  }
Qed.

(* TODO: make generic *)
Lemma equiv_smt_expr_normalize_cmpop_bv32 : forall op (ast1 ast2 : smt_ast Sort_BV32),
  equiv_smt_expr
    (Expr Sort_BV1 (normalize_cmpop op Sort_BV32 ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp Sort_BV32 op ast1 ast2)).
Proof.
  intros op ast1 ast2.
  destruct op;
  try apply equiv_smt_expr_refl;
  (
    simpl;
    apply equiv_smt_expr_symmetry;
    try apply equiv_smt_expr_ne_to_eq;
    try apply equiv_smt_expr_ugt_ult;
    try apply equiv_smt_expr_uge_ule;
    try apply equiv_smt_expr_sgt_slt;
    try apply equiv_smt_expr_sge_sle
  ).
  {
    dependent destruction ast2;
    try apply equiv_smt_expr_refl.
    {
      dependent destruction ast1;
      try apply equiv_smt_expr_refl;
      try apply equiv_smt_expr_eq_comm.
    }
  }
  {
    dependent destruction ast2;
    try (
      eapply equiv_smt_expr_transitivity;
      [ eapply equiv_smt_expr_ne_to_eq | apply equiv_smt_expr_refl ]
    ).
    {
      eapply equiv_smt_expr_transitivity.
      { eapply equiv_smt_expr_ne_to_eq. }
      {
        apply equiv_smt_expr_cmpop.
        { apply equiv_smt_expr_refl. }
        { apply equiv_smt_expr_eq_comm. }
      }
    }
  }
Qed.

(* TODO: avoid duplicate proof *)
Lemma equiv_smt_expr_normalize_cmpop_bv64 : forall op (ast1 ast2 : smt_ast Sort_BV64),
  equiv_smt_expr
    (Expr Sort_BV1 (normalize_cmpop op Sort_BV64 ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp Sort_BV64 op ast1 ast2)).
Proof.
  intros op ast1 ast2.
  destruct op;
  try apply equiv_smt_expr_refl;
  (
    simpl;
    apply equiv_smt_expr_symmetry;
    try apply equiv_smt_expr_ne_to_eq;
    try apply equiv_smt_expr_ugt_ult;
    try apply equiv_smt_expr_uge_ule;
    try apply equiv_smt_expr_sgt_slt;
    try apply equiv_smt_expr_sge_sle
  ).
  {
    dependent destruction ast2;
    try apply equiv_smt_expr_refl.
    {
      dependent destruction ast1;
      try apply equiv_smt_expr_refl;
      try apply equiv_smt_expr_eq_comm.
    }
  }
  {
    dependent destruction ast2;
    try (
      eapply equiv_smt_expr_transitivity;
      [ eapply equiv_smt_expr_ne_to_eq | apply equiv_smt_expr_refl ]
    ).
    {
      eapply equiv_smt_expr_transitivity.
      { eapply equiv_smt_expr_ne_to_eq. }
      {
        apply equiv_smt_expr_cmpop.
        { apply equiv_smt_expr_refl. }
        { apply equiv_smt_expr_eq_comm. }
      }
    }
  }
Qed.

Lemma equiv_smt_expr_normalize_cmpop : forall s op (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (normalize_cmpop op s ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s op ast1 ast2)).
Proof.
  intros s op ast1 ast2.
  destruct s;
  try apply equiv_smt_expr_refl.
  { apply equiv_smt_expr_normalize_cmpop_bv1. }
  { apply equiv_smt_expr_normalize_cmpop_bv32. }
  { apply equiv_smt_expr_normalize_cmpop_bv64. }
Qed.

Lemma equiv_smt_expr_normalize_cmpop_args : forall s op (ast1 ast2 : smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s (normalize s ast1)) ->
  equiv_smt_expr (Expr s ast2) (Expr s (normalize s ast2)) ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s op ast1 ast2))
    (Expr Sort_BV1 (normalize_cmpop op s (normalize s ast1) (normalize s ast2))).
Proof.
  intros s op ast1 ast2 H1 H2.
  apply equiv_smt_expr_symmetry.
  eapply equiv_smt_expr_transitivity.
  { apply equiv_smt_expr_normalize_cmpop. }
  {
    apply equiv_smt_expr_cmpop;
    apply equiv_smt_expr_symmetry; assumption.
  }
Qed.

Lemma equiv_smt_expr_normalize_not : forall s (ast : smt_ast s),
  equiv_smt_expr
    (Expr s (normalize_not s ast))
    (Expr s (AST_Not s ast)).
Proof.
  intros s ast.
  destruct s;
  try apply equiv_smt_expr_refl.
  {
    simpl.
    apply EquivExpr.
    intros m.
    simpl.
    remember (smt_eval_ast m Sort_BV1 ast) as n.
    assert(L: n = Int1.zero \/ n = Int1.one).
    { apply int1_destruct. }
    destruct L as [L | L];
    (
      rewrite L;
      unfold smt_eval_cmpop_by_sort;
      unfold smt_eval_cmpop_generic;
      reflexivity
    ).
  }
Qed.

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
    { apply equiv_smt_expr_normalize_binop_args; assumption. }
    {
      apply equiv_smt_expr_binop with (ast1 := ast1) (ast3 := ast2); assumption.
    }
  }
  {
    (* TODO: avoid duplicate blocks *)
    destruct s.
    { apply equiv_smt_expr_normalize_cmpop_args; try assumption. }
    {
      simpl.
      unfold normalize_cmpop_bv8.
      apply equiv_smt_expr_cmpop with (ast1 := ast1) (ast3 := ast2); assumption.
    }
    {
      simpl.
      unfold normalize_cmpop_bv16.
      apply equiv_smt_expr_cmpop with (ast1 := ast1) (ast3 := ast2); assumption.
    }
    { apply equiv_smt_expr_normalize_cmpop_args; try assumption. }
    { apply equiv_smt_expr_normalize_cmpop_args; try assumption. }
  }
  {
    destruct s;
    try (
      simpl;
      apply equiv_smt_expr_not;
      assumption
    ).
    {
      eapply equiv_smt_expr_transitivity.
      {
        apply equiv_smt_expr_symmetry.
        apply equiv_smt_expr_normalize_not.
      }
      {
        apply equiv_smt_expr_cmpop.
        { apply equiv_smt_expr_refl. }
        { assumption. }
      }
    }
  }
  {
    unfold normalize_zext.
    apply equiv_smt_expr_zext.
    assumption.
  }
  {
    unfold normalize_sext.
    apply equiv_smt_expr_sext.
    assumption.
  }
  {
    unfold normalize_extract.
    apply equiv_smt_expr_extract.
    assumption.
  }
  { apply equiv_smt_expr_refl.  }
Qed.

Definition sort_to_add s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.add
  | Sort_BV8 => Int8.add
  | Sort_BV16 => Int16.add
  | Sort_BV32 => Int32.add
  | Sort_BV64 => Int64.add
  end
.

Definition sort_to_sub s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.sub
  | Sort_BV8 => Int8.sub
  | Sort_BV16 => Int16.sub
  | Sort_BV32 => Int32.sub
  | Sort_BV64 => Int64.sub
  end
.

Definition sort_to_mul s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.mul
  | Sort_BV8 => Int8.mul
  | Sort_BV16 => Int16.mul
  | Sort_BV32 => Int32.mul
  | Sort_BV64 => Int64.mul
  end
.

Definition sort_to_udiv s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.divu
  | Sort_BV8 => Int8.divu
  | Sort_BV16 => Int16.divu
  | Sort_BV32 => Int32.divu
  | Sort_BV64 => Int64.divu
  end
.

Definition sort_to_sdiv s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.divs
  | Sort_BV8 => Int8.divs
  | Sort_BV16 => Int16.divs
  | Sort_BV32 => Int32.divs
  | Sort_BV64 => Int64.divs
  end
.

Definition sort_to_urem s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.modu
  | Sort_BV8 => Int8.modu
  | Sort_BV16 => Int16.modu
  | Sort_BV32 => Int32.modu
  | Sort_BV64 => Int64.modu
  end
.

Definition sort_to_srem s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.mods
  | Sort_BV8 => Int8.mods
  | Sort_BV16 => Int16.mods
  | Sort_BV32 => Int32.mods
  | Sort_BV64 => Int64.mods
  end
.

Definition sort_to_xor s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.xor
  | Sort_BV8 => Int8.xor
  | Sort_BV16 => Int16.xor
  | Sort_BV32 => Int32.xor
  | Sort_BV64 => Int64.xor
  end
.
Definition sort_to_shl s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.shl
  | Sort_BV8 => Int8.shl
  | Sort_BV16 => Int16.shl
  | Sort_BV32 => Int32.shl
  | Sort_BV64 => Int64.shl
  end
.

Definition sort_to_lshr s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.shru
  | Sort_BV8 => Int8.shru
  | Sort_BV16 => Int16.shru
  | Sort_BV32 => Int32.shru
  | Sort_BV64 => Int64.shru
  end
.

Definition sort_to_ashr s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.shr
  | Sort_BV8 => Int8.shr
  | Sort_BV16 => Int16.shr
  | Sort_BV32 => Int32.shr
  | Sort_BV64 => Int64.shr
  end
.

Definition sort_to_and s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.and
  | Sort_BV8 => Int8.and
  | Sort_BV16 => Int16.and
  | Sort_BV32 => Int32.and
  | Sort_BV64 => Int64.and
  end
.

Definition sort_to_or s : (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.or
  | Sort_BV8 => Int8.or
  | Sort_BV16 => Int16.or
  | Sort_BV32 => Int32.or
  | Sort_BV64 => Int64.or
  end
.

Lemma equiv_smt_expr_add_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_add s) n1 n2)))
    (Expr s (AST_BinOp s SMT_Add (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_sub_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_sub s) n1 n2)))
    (Expr s (AST_BinOp s SMT_Sub (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_mul_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_mul s) n1 n2)))
    (Expr s (AST_BinOp s SMT_Mul (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_udiv_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_udiv s) n1 n2)))
    (Expr s (AST_BinOp s SMT_UDiv (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_sdiv_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_sdiv s) n1 n2)))
    (Expr s (AST_BinOp s SMT_SDiv (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_urem_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_urem s) n1 n2)))
    (Expr s (AST_BinOp s SMT_URem (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_srem_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_srem s) n1 n2)))
    (Expr s (AST_BinOp s SMT_SRem (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_xor_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_xor s) n1 n2)))
    (Expr s (AST_BinOp s SMT_Xor (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_shl_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_shl s) n1 n2)))
    (Expr s (AST_BinOp s SMT_Shl (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_lshr_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_lshr s) n1 n2)))
    (Expr s (AST_BinOp s SMT_LShr (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_ashr_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_ashr s) n1 n2)))
    (Expr s (AST_BinOp s SMT_AShr (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_and_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_and s) n1 n2)))
    (Expr s (AST_BinOp s SMT_And (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_or_fold_consts : forall s (n1 n2 : smt_sort_to_int_type s),
  equiv_smt_expr
    (Expr s (AST_Const s ((sort_to_or s) n1 n2)))
    (Expr s (AST_BinOp s SMT_Or (AST_Const s n1) (AST_Const s n2))).
Proof.
  intros s n1 n2.
  destruct s;
  try (
    apply EquivExpr;
    intros m;
    simpl;
    reflexivity
  ).
Qed.

Lemma equiv_smt_expr_simplify_and_bv1 : forall n ast,
  equiv_smt_expr
    (Expr Sort_BV1
       (if Int1.eq n Int1.zero then smt_ast_false else ast))
    (Expr Sort_BV1
       (AST_BinOp Sort_BV1 SMT_And (AST_Const Sort_BV1 n) ast)).
Proof.
  intros n ast.
  apply EquivExpr.
  intros m.
  simpl.
  assert(L: n = Int1.zero \/ n = Int1.one).
  { apply int1_destruct. }
  destruct L as [L | L]; subst; simpl.
  {
    rewrite Int1.and_zero_l.
    reflexivity.
  }
  {
    replace Int1.one with Int1.mone.
    {
      rewrite Int1.and_mone_l.
      reflexivity.
    }
    { apply int1_eqb_eq. reflexivity. }
  }
Qed.

Lemma equiv_smt_expr_simplify_binop_bv1 : forall op (ast1 ast2 : smt_ast Sort_BV1),
  equiv_smt_expr
    (Expr Sort_BV1 (simplify_binop_bv1 op ast1 ast2))
    (Expr Sort_BV1 (AST_BinOp Sort_BV1 op ast1 ast2)).
Proof.
  intros op ast1 ast2.
  dependent destruction ast1;
  try (
    dependent destruction ast2;
    try apply equiv_smt_expr_refl;
    (
      destruct op;
      try apply equiv_smt_expr_refl;
      (
        simpl;
        eapply equiv_smt_expr_transitivity;
        [ apply equiv_smt_expr_simplify_and_bv1 | apply equiv_smt_expr_and_comm ]
      )
    )
  ).
  (* const *)
  {
    dependent destruction ast2;
    try (
      simpl;
      destruct op;
      try apply equiv_smt_expr_refl;
      apply equiv_smt_expr_simplify_and_bv1
    ).
    (* const *)
    {
      simpl.
      destruct op;
      try apply equiv_smt_expr_refl.
      { apply equiv_smt_expr_add_fold_consts. }
      { apply equiv_smt_expr_sub_fold_consts. }
      { apply equiv_smt_expr_mul_fold_consts. }
      { apply equiv_smt_expr_and_fold_consts. }
    }
  }
Qed.

Lemma equiv_smt_expr_add_zero_bv32 : forall n ast,
  equiv_smt_expr
    (Expr Sort_BV32
       (if Int32.eq n Int32.zero
          then ast
        else
         AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n) ast))
    (Expr Sort_BV32 (AST_BinOp Sort_BV32 SMT_Add (AST_Const Sort_BV32 n) ast)).
Proof.
  intros n ast.
  apply EquivExpr.
  intros m.
  simpl.
  remember (Int32.eq n Int32.zero) as b.
  destruct b; symmetry in Heqb.
  {
    apply int32_eqb_eq in Heqb.
    rewrite Heqb.
    simpl.
    rewrite Int32.add_zero_l.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
Qed.

Lemma equiv_smt_expr_or_zero_left_bv32 : forall n ast,
  equiv_smt_expr
    (Expr Sort_BV32
       (if Int32.eq n Int32.zero
          then ast
        else
         AST_BinOp Sort_BV32 SMT_Or (AST_Const Sort_BV32 n) ast))
    (Expr Sort_BV32 (AST_BinOp Sort_BV32 SMT_Or (AST_Const Sort_BV32 n) ast)).
Proof.
Admitted.

Lemma equiv_smt_expr_or_zero_right_bv32 : forall n ast,
  equiv_smt_expr
    (Expr Sort_BV32
       (if Int32.eq n Int32.zero
          then ast
        else
         AST_BinOp Sort_BV32 SMT_Or ast (AST_Const Sort_BV32 n)))
    (Expr Sort_BV32 (AST_BinOp Sort_BV32 SMT_Or ast (AST_Const Sort_BV32 n))).
Proof.
Admitted.

Lemma equiv_smt_expr_simplify_binop_bv32 : forall op (ast1 ast2 : smt_ast Sort_BV32),
  equiv_smt_expr
    (Expr Sort_BV32 (simplify_binop_bv32 op ast1 ast2))
    (Expr Sort_BV32 (AST_BinOp Sort_BV32 op ast1 ast2)).
Proof.
  intros op ast1 ast2.
  dependent destruction ast1;
  try (
    destruct op;
    try (
      dependent destruction ast2;
      try apply equiv_smt_expr_refl
    );
    apply equiv_smt_expr_or_zero_right_bv32
  ).
  (* const *)
  {
    dependent destruction ast2;
    try (
      simpl;
      destruct op;
      try apply equiv_smt_expr_refl; [
        apply equiv_smt_expr_add_zero_bv32 |
        apply equiv_smt_expr_or_zero_left_bv32
      ]
    ).
    (* const *)
    {
      simpl.
      destruct op;
      try apply equiv_smt_expr_refl.
      { apply equiv_smt_expr_add_fold_consts. }
      { apply equiv_smt_expr_sub_fold_consts. }
      { apply equiv_smt_expr_mul_fold_consts. }
      { apply equiv_smt_expr_udiv_fold_consts. }
      { apply equiv_smt_expr_sdiv_fold_consts. }
      { apply equiv_smt_expr_urem_fold_consts. }
      { apply equiv_smt_expr_srem_fold_consts. }
      { apply equiv_smt_expr_and_fold_consts. }
      { apply equiv_smt_expr_or_fold_consts. }
      { apply equiv_smt_expr_xor_fold_consts. }
      { apply equiv_smt_expr_shl_fold_consts. }
      { apply equiv_smt_expr_lshr_fold_consts. }
      { apply equiv_smt_expr_ashr_fold_consts. }
    }
  }
Qed.

Lemma equiv_smt_expr_simplify_binop : forall s op (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr s (simplify_binop op s ast1 ast2))
    (Expr s (AST_BinOp s op ast1 ast2)).
Proof.
  intros s op ast1 ast2.
  destruct s.
  { apply equiv_smt_expr_simplify_binop_bv1. }
  { apply equiv_smt_expr_refl. }
  { apply equiv_smt_expr_refl. }
  { apply equiv_smt_expr_simplify_binop_bv32. }
  { apply equiv_smt_expr_refl. }
Qed.

Lemma equiv_smt_expr_simplify_cmpop_bv1 : forall op (ast1 ast2 : smt_ast Sort_BV1),
  equiv_smt_expr
    (Expr Sort_BV1 (simplify_cmpop_bv1 op ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp Sort_BV1 op ast1 ast2)).
Proof.
  intros op ast1 ast2.
  dependent destruction ast1; dependent destruction ast2;
  try apply equiv_smt_expr_refl.
  {
    simpl.
    apply EquivExpr.
    intros m.
    simpl.
    unfold smt_eval_cmpop_by_sort.
    remember (smt_eval_cmpop_generic op n n0) as b.
    destruct op;
    try (
      simpl in *;
      unfold smt_eval_cmpop_by_sort;
      simpl;
      destruct b;
      (rewrite <- Heqb; reflexivity)
    ).
  }
  {
    destruct op0;
    try (destruct s; apply equiv_smt_expr_refl).
    {
      dependent destruction ast2_1;
      try (destruct s; apply equiv_smt_expr_refl);
      (* zext/sext *)
      try (
        destruct cast_sort;
        try apply equiv_smt_expr_refl
      ).
      {
        destruct op;
        try (destruct s; apply equiv_smt_expr_refl).
        {
          simpl.
          destruct s;
          try apply equiv_smt_expr_refl.
          {
            simpl.
            apply EquivExpr.
            intros m.
            remember (Int1.eq n Int1.zero) as b1.
            remember (Int1.eq n0 Int1.zero) as b2.
            destruct b1, b2; symmetry in Heqb1, Heqb2;
            try reflexivity.
            {
              apply int1_eqb_eq in Heqb1, Heqb2.
              subst.
              simpl.
              unfold smt_eval_cmpop_by_sort.
              unfold smt_eval_cmpop_generic.
              simpl.
              remember (smt_eval_ast m Sort_BV1 ast2_2) as n.
              assert(L: n = Int1.zero \/ n = Int1.one).
              { apply int1_destruct. }
              destruct L as [L | L].
              { rewrite L. simpl. reflexivity. }
              { rewrite L. simpl. reflexivity. }
            }
          }
        }
      }
    }
  }
Qed.

Lemma equiv_smt_expr_simplify_cmpop_bv32 : forall op (ast1 ast2 : smt_ast Sort_BV32),
  equiv_smt_expr
    (Expr Sort_BV1 (simplify_cmpop_bv32 op ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp Sort_BV32 op ast1 ast2)).
Proof.
  intros op ast1 ast2.
  dependent destruction ast1; dependent destruction ast2;
  try apply equiv_smt_expr_refl.
  {
    simpl.
    apply EquivExpr.
    intros m.
    simpl.
    unfold smt_eval_cmpop_by_sort.
    remember (smt_eval_cmpop_generic op n n0) as b.
    destruct op;
    try (
      simpl in *;
      unfold smt_eval_cmpop_by_sort;
      simpl;
      destruct b;
      (rewrite <- Heqb; reflexivity)
    ).
  }
Qed.

(* TODO: avoid duplicate proof *)
Lemma equiv_smt_expr_simplify_cmpop_bv64 : forall op (ast1 ast2 : smt_ast Sort_BV64),
  equiv_smt_expr
    (Expr Sort_BV1 (simplify_cmpop_bv64 op ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp Sort_BV64 op ast1 ast2)).
Proof.
  intros op ast1 ast2.
  dependent destruction ast1; dependent destruction ast2;
  try apply equiv_smt_expr_refl.
  {
    simpl.
    apply EquivExpr.
    intros m.
    simpl.
    unfold smt_eval_cmpop_by_sort.
    remember (smt_eval_cmpop_generic op n n0) as b.
    destruct op;
    try (
      simpl in *;
      unfold smt_eval_cmpop_by_sort;
      simpl;
      destruct b;
      (rewrite <- Heqb; reflexivity)
    ).
  }
Qed.

Lemma equiv_smt_expr_simplify_cmpop : forall s op (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (simplify_cmpop op s ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s op ast1 ast2)).
Proof.
  intros s op ast1 ast2.
  destruct s.
  { apply equiv_smt_expr_simplify_cmpop_bv1. }
  { apply equiv_smt_expr_refl. }
  { apply equiv_smt_expr_refl. }
  { apply equiv_smt_expr_simplify_cmpop_bv32. }
  { apply equiv_smt_expr_simplify_cmpop_bv64. }
Qed.

Lemma equiv_smt_expr_simplify_zext : forall s (ast : smt_ast s) cast_sort,
  equiv_smt_expr
    (Expr cast_sort (simplify_zext s ast cast_sort))
    (Expr cast_sort (AST_ZExt s ast cast_sort)).
Proof.
  intros s ast cast_sort.
  dependent destruction ast;
  try apply equiv_smt_expr_refl.
  simpl.
  apply EquivExpr.
  intros m.
  simpl.
  reflexivity.
Qed.

Lemma equiv_smt_expr_simplify_sext : forall s (ast : smt_ast s) cast_sort,
  equiv_smt_expr
    (Expr cast_sort (simplify_sext s ast cast_sort))
    (Expr cast_sort (AST_SExt s ast cast_sort)).
Proof.
  intros s ast cast_sort.
  dependent destruction ast;
  try apply equiv_smt_expr_refl.
  simpl.
  apply EquivExpr.
  intros m.
  simpl.
  reflexivity.
Qed.

Lemma equiv_smt_expr_simplify_extract : forall s (ast : smt_ast s) cast_sort,
  equiv_smt_expr
    (Expr cast_sort (simplify_extract s ast cast_sort))
    (Expr cast_sort (AST_Extract s ast cast_sort)).
Proof.
  intros s ast cast_sort.
  dependent destruction ast;
  try apply equiv_smt_expr_refl.
  simpl.
  apply EquivExpr.
  intros m.
  simpl.
  reflexivity.
Qed.

Lemma equiv_smt_expr_simplify: forall s (ast : smt_ast s),
  equiv_smt_expr
    (Expr s ast)
    (Expr s (simplify s ast)).
Proof.
  intros s ast.
  induction ast; simpl.
  { apply equiv_smt_expr_refl. }
  { apply equiv_smt_expr_refl. }
  {
    apply equiv_smt_expr_symmetry.
    eapply equiv_smt_expr_transitivity.
    { apply equiv_smt_expr_simplify_binop. }
    {
      apply equiv_smt_expr_binop;
      apply equiv_smt_expr_symmetry; assumption.
    }
  }
  {
    apply equiv_smt_expr_symmetry.
    eapply equiv_smt_expr_transitivity.
    { apply equiv_smt_expr_simplify_cmpop. }
    {
      apply equiv_smt_expr_cmpop;
      apply equiv_smt_expr_symmetry; assumption.
    }
  }
  {
    apply equiv_smt_expr_not.
    assumption.
  }
  {
    apply equiv_smt_expr_symmetry.
    eapply equiv_smt_expr_transitivity.
    { apply equiv_smt_expr_simplify_zext. }
    {
      apply equiv_smt_expr_zext.
      apply equiv_smt_expr_symmetry.
      assumption.
    }
  }
  {
    apply equiv_smt_expr_symmetry.
    eapply equiv_smt_expr_transitivity.
    { apply equiv_smt_expr_simplify_sext. }
    {
      apply equiv_smt_expr_sext.
      apply equiv_smt_expr_symmetry.
      assumption.
    }
  }
  {
    apply equiv_smt_expr_symmetry.
    eapply equiv_smt_expr_transitivity.
    { apply equiv_smt_expr_simplify_extract. }
    {
      apply equiv_smt_expr_extract.
      apply equiv_smt_expr_symmetry.
      assumption.
    }
  }
  { apply equiv_smt_expr_refl. }
Qed.

Lemma equiv_smt_expr_normalize_simplify: forall s (ast : smt_ast s),
  equiv_smt_expr
    (Expr s ast)
    (Expr s (simplify s (normalize s ast))).
Proof.
  intros s ast.
  eapply equiv_smt_expr_transitivity.
  { apply equiv_smt_expr_normalize. }
  { apply equiv_smt_expr_simplify. }
Qed.
