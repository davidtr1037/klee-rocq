From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE.Numeric Require Import Integers.

(*
From SE Require Import Maps.
Definition smt_model := total_map nat.
Definition default_model := empty_map 0
*)

Inductive smt_expr : Set :=
  | SMT_BV_I1 (n : int1)
  | SMT_BV_I8 (n : int8)
  | SMT_BV_I16 (n : int16)
  | SMT_BV_I32 (n : int32)
  | SMT_BV_I64 (n : int64)
  | SMT_Add (e1 e2 : smt_expr)
  | SMT_Sub (e1 e2 : smt_expr)
  | SMT_Mul (e1 e2 : smt_expr)
  | SMT_UDiv (e1 e2 : smt_expr)
  | SMT_SDiv (e1 e2 : smt_expr)
  | SMT_URem (e1 e2 : smt_expr)
  | SMT_SRem (e1 e2 : smt_expr)
  | SMT_And (e1 e2 : smt_expr)
  | SMT_Or (e1 e2 : smt_expr)
  | SMT_Xor (e1 e2 : smt_expr)
  | SMT_Shl (e1 e2 : smt_expr)
  | SMT_LShr (e1 e2 : smt_expr)
  | SMT_AShr (e1 e2 : smt_expr)
  | SMT_Eq (e1 e2 : smt_expr)
  | SMT_Ne (e1 e2 : smt_expr)
  | SMT_Ult (e1 e2 : smt_expr)
  | SMT_Ule (e1 e2 : smt_expr)
  | SMT_Ugt (e1 e2 : smt_expr)
  | SMT_Uge (e1 e2 : smt_expr)
  | SMT_Slt (e1 e2 : smt_expr)
  | SMT_Sle (e1 e2 : smt_expr)
  | SMT_Sgt (e1 e2 : smt_expr)
  | SMT_Sge (e1 e2 : smt_expr)
  | SMT_ZExt (e : smt_expr)
  | SMT_SExt (e : smt_expr)
  | SMT_Not (e : smt_expr)
  | ZExt_Concat (e1 e2 : smt_expr)
  | ZExt_Extract (e : smt_expr) (o w : nat)
.
