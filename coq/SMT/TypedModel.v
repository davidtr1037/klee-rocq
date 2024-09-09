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

Definition smt_eval_cmpop_generic {Int} `{VInt Int} (op : smt_cmpop) (x y : Int) : bool :=
  match op with
   | SMT_Eq => cmp Ceq x y
   | SMT_Ne => cmp Cne x y
   | SMT_Ugt => cmpu Cgt x y
   | SMT_Uge => cmpu Cge x y
   | SMT_Ult => cmpu Clt x y
   | SMT_Ule => cmpu Cle x y
   | SMT_Sgt => cmp Cgt x y
   | SMT_Sge => cmp Cge x y
   | SMT_Slt => cmp Clt x y
   | SMT_Sle => cmp Cle x y
   end
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

Fixpoint smt_eval_internal (m : typed_smt_model) (s : smt_sort) (ast : typed_smt_ast s) : (smt_sort_to_int_type s) :=
  match ast with
  | TypedSMT_Const arg_sort n => n
  | TypedSMT_Var arg_sort x => create_int_by_sort arg_sort ((bv_model m) x)
  | TypedSMT_BinOp arg_sort op ast1 ast2 =>
      smt_eval_binop_by_sort
        op
        arg_sort
        (smt_eval_internal m arg_sort ast1)
        (smt_eval_internal m arg_sort ast2)
  | TypedSMT_CmpOp arg_sort op ast1 ast2 =>
      smt_eval_cmpop_by_sort
        op
        arg_sort
        (smt_eval_internal m arg_sort ast1)
        (smt_eval_internal m arg_sort ast2)
  | TypedSMT_Not arg_sort ast => smt_eval_not_by_sort arg_sort (smt_eval_internal m arg_sort ast)
  end
.
