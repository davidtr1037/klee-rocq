From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE Require Import DynamicValue.

From SE.Numeric Require Import Integers.

From SE.SMT Require Import TypedExpr.

From SE.Utils Require Import StringMap.

Inductive symbol : Type :=
  | Symbol_BV (s : string)
.

Record typed_smt_model := mk_smt_model {
  bv_model : total_map Z;
}.

Definition default_model := mk_smt_model (empty_map 0%Z).

Definition create_int_by_sort (s : smt_sort) (n : Z) : (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.repr n
  | Sort_BV8 => Int8.repr n
  | Sort_BV16 => Int16.repr n
  | Sort_BV32 => Int32.repr n
  | Sort_BV64 => Int64.repr n
  end
.

Definition smt_eval_binop_generic {Int} `{VInt Int} (op : smt_binop) (x y : Int) : Int :=
  match op with
  | SMT_Add => (add x y)
  | SMT_Sub => (sub x y)
  | SMT_Mul => (mul x y)
  | SMT_UDiv => (divu x y)
  | SMT_SDiv => (divs x y)
  | SMT_URem => (modu x y)
  | SMT_SRem => (mods x y)
  | SMT_And => (and x y)
  | SMT_Or => (or x y)
  | SMT_Xor => (xor x y)
  | SMT_Shl => (shl x y)
  | SMT_LShr => (shru x y)
  | SMT_AShr => (shr x y)
  end
.

Definition binop_predicate (s : smt_sort) :=
  smt_binop -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s)
.

Definition smt_eval_binop_by_sort op s (x y : (smt_sort_to_int_type s)) : (smt_sort_to_int_type s) :=
  let f :=
    match s return (binop_predicate s) with
    | Sort_BV1 => smt_eval_binop_generic
    | Sort_BV8 => smt_eval_binop_generic
    | Sort_BV16 => smt_eval_binop_generic
    | Sort_BV32 => smt_eval_binop_generic
    | Sort_BV64 => smt_eval_binop_generic
    end in
  f op x y
.

Definition smt_cmpop_to_comparison (op : smt_cmpop) : comparison :=
  match op with
  | SMT_Eq => Ceq
  | SMT_Ne => Cne
  | SMT_Ugt => Cgt
  | SMT_Uge => Cge
  | SMT_Ult => Clt
  | SMT_Ule => Cle
  | SMT_Sgt => Cgt
  | SMT_Sge => Cge
  | SMT_Slt => Clt
  | SMT_Sle => Cle
  end
.
Definition smt_eval_cmpop_generic {Int} `{VInt Int} (op : smt_cmpop) (x y : Int) : bool :=
  cmp (smt_cmpop_to_comparison op) x y
.

Definition cmpop_predicate (s : smt_sort) :=
  smt_cmpop -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> bool
.

Definition smt_eval_cmpop_by_sort op s (x y : (smt_sort_to_int_type s)) : int1 :=
  let f :=
    match s return (cmpop_predicate s) with
    | Sort_BV1 => smt_eval_cmpop_generic
    | Sort_BV8 => smt_eval_cmpop_generic
    | Sort_BV16 => smt_eval_cmpop_generic
    | Sort_BV32 => smt_eval_cmpop_generic
    | Sort_BV64 => smt_eval_cmpop_generic
    end in
  if (f op x y) then one else zero
.

Definition create_mone_by_sort (s : smt_sort) : (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.mone
  | Sort_BV8 => Int8.mone
  | Sort_BV16 => Int16.mone
  | Sort_BV32 => Int32.mone
  | Sort_BV64 => Int64.mone
  end
.

Definition smt_eval_not_by_sort s (x : (smt_sort_to_int_type s)) : (smt_sort_to_int_type s) :=
  smt_eval_binop_by_sort SMT_Xor s x (create_mone_by_sort s)
.

Fixpoint smt_eval_ast (m : typed_smt_model) (s : smt_sort) (ast : typed_smt_ast s) : (smt_sort_to_int_type s) :=
  match ast with
  | TypedAST_Const arg_sort n => n
  | TypedAST_Var arg_sort x => create_int_by_sort arg_sort ((bv_model m) x)
  | TypedAST_BinOp arg_sort op ast1 ast2 =>
      smt_eval_binop_by_sort
        op
        arg_sort
        (smt_eval_ast m arg_sort ast1)
        (smt_eval_ast m arg_sort ast2)
  | TypedAST_CmpOp arg_sort op ast1 ast2 =>
      smt_eval_cmpop_by_sort
        op
        arg_sort
        (smt_eval_ast m arg_sort ast1)
        (smt_eval_ast m arg_sort ast2)
  | TypedAST_Not arg_sort ast =>
      smt_eval_not_by_sort arg_sort (smt_eval_ast m arg_sort ast)
  end
.

Definition smt_eval (m : typed_smt_model) (e : typed_smt_expr) : (smt_sort_to_int_type (get_sort e)) :=
  match e with
  | TypedSMTExpr sort ast => smt_eval_ast m sort ast
  end
.

Definition sat_via (ast : smt_ast_i1) (m : typed_smt_model) :=
  smt_eval_ast m Sort_BV1 ast = one
.

Definition sat (ast : smt_ast_i1) :=
  exists (m : typed_smt_model), sat_via ast m
.

Definition unsat (ast : smt_ast_i1) := ~ sat ast.

Lemma unsat_and : forall (e1 e2 : smt_ast_i1),
  unsat e1 ->
  unsat (TypedAST_BinOp Sort_BV1 SMT_And e1 e2).
Proof.
Admitted.

Lemma subexpr_non_interference : forall sort (ast : typed_smt_ast sort) x m n,
  (~ contains_var (TypedSMTExpr sort ast) x ) ->
  smt_eval_ast m sort ast = smt_eval_ast (mk_smt_model (x !-> n; bv_model m)) sort ast.
Proof.
Admitted.

Inductive equiv_typed_smt_expr : typed_smt_expr -> typed_smt_expr -> Prop :=
  | EquivTypedSMTExpr : forall s (ast1 ast2 : typed_smt_ast s),
      (forall m, smt_eval_ast m s ast1 = smt_eval_ast m s ast2) ->
      equiv_typed_smt_expr (TypedSMTExpr s ast1) (TypedSMTExpr s ast2)
.

Lemma equiv_typed_smt_expr_refl : forall e, equiv_typed_smt_expr e e.
Proof.
Admitted.

Lemma equiv_typed_smt_expr_symmetry : forall e1 e2,
  equiv_typed_smt_expr e1 e2 -> equiv_typed_smt_expr e2 e1.
Proof.
Admitted.

Lemma equiv_typed_smt_expr_transitivity : forall e1 e2 e3,
  equiv_typed_smt_expr e1 e2 -> equiv_typed_smt_expr e2 e3 -> equiv_typed_smt_expr e1 e3.
Proof.
Admitted.

Lemma equiv_typed_smt_expr_unsat : forall (ast1 ast2 : smt_ast_i1),
  equiv_typed_smt_expr (TypedSMTExpr Sort_BV1 ast1) (TypedSMTExpr Sort_BV1 ast2) ->
  unsat ast1 ->
  unsat ast2.
Proof.
Admitted.

Lemma equiv_typed_smt_expr_binop : forall s op (ast1 ast2 ast3 ast4 : typed_smt_ast s),
  equiv_typed_smt_expr (TypedSMTExpr s ast1) (TypedSMTExpr s ast2) ->
  equiv_typed_smt_expr (TypedSMTExpr s ast3) (TypedSMTExpr s ast4) ->
  equiv_typed_smt_expr
    (TypedSMTExpr s (TypedAST_BinOp s op ast1 ast3))
    (TypedSMTExpr s (TypedAST_BinOp s op ast2 ast4)).
Proof.
Admitted.

Lemma equiv_typed_smt_expr_not : forall s (ast1 ast2 : typed_smt_ast s),
  equiv_typed_smt_expr (TypedSMTExpr s ast1) (TypedSMTExpr s ast2) ->
  equiv_typed_smt_expr
    (TypedSMTExpr s (TypedAST_Not s ast1))
    (TypedSMTExpr s (TypedAST_Not s ast2)).
Proof.
Admitted.

(* TODO: define lemmas for cmpop *)

Definition normalize (e : typed_smt_expr) : typed_smt_expr :=
  e
.

Definition simplify (e : typed_smt_expr) : typed_smt_expr :=
  e
.
