From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE Require Import DynamicValue.
From SE.Numeric Require Import Integers.

Variant smt_binop : Type :=
  | SMT_Add
  | SMT_Sub
  | SMT_Mul
  | SMT_UDiv
  | SMT_SDiv
  | SMT_URem
  | SMT_SRem
  | SMT_And
  | SMT_Or
  | SMT_Xor
  | SMT_Shl
  | SMT_LShr
  | SMT_AShr
.

Variant smt_cmpop : Type :=
  | SMT_Eq
  | SMT_Ne
  | SMT_Ult
  | SMT_Ule
  | SMT_Ugt
  | SMT_Uge
  | SMT_Slt
  | SMT_Sle
  | SMT_Sgt
  | SMT_Sge
.

(* TODO: the type of width should be positive? *)
Inductive smt_expr : Type :=
  | SMT_Const_I1 (n : int1)
  | SMT_Const_I8 (n : int8)
  | SMT_Const_I16 (n : int16)
  | SMT_Const_I32 (n : int32)
  | SMT_Const_I64 (n : int64)
  | SMT_Var_I1 (x : string)
  | SMT_Var_I8 (x : string)
  | SMT_Var_I16 (x : string)
  | SMT_Var_I32 (x : string)
  | SMT_Var_I64 (x : string)
  | SMT_BinOp (op : smt_binop) (e1 e2 : smt_expr)
  | SMT_CmpOp (op : smt_cmpop) (e1 e2 : smt_expr)
  | SMT_ZExt (e : smt_expr) (w : positive)
  | SMT_SExt (e : smt_expr) (w : positive)
  | SMT_ITE (e1 e2 e3 : smt_expr)
  | SMT_Not (e : smt_expr)
  | SMT_Concat (e1 e2 : smt_expr)
  | SMT_Extract (e : smt_expr) (i : N) (w : positive)
  | SMT_Select (a : smt_array) (e : smt_expr)
  with smt_array : Type :=
    | SMT_Array (x : string)
    | SMT_Store (a : smt_array) (i e : smt_expr)
.

Definition SMT_True := SMT_Const_I1 one.
Definition SMT_False := SMT_Const_I1 zero.

Inductive smt_sort : Type :=
  | Sort_BV1
  | Sort_BV8
  | Sort_BV16
  | Sort_BV32
  | Sort_BV64
  | Sort_Array
.

Definition make_smt_const (bits : positive) (n : Z) : option smt_expr :=
  match bits with
  | 1%positive => Some (SMT_Const_I1 (Int1.repr n))
  | 8%positive => Some (SMT_Const_I8 (Int8.repr n))
  | 16%positive => Some (SMT_Const_I16 (Int16.repr n))
  | 32%positive => Some (SMT_Const_I32 (Int32.repr n))
  | 64%positive => Some (SMT_Const_I64 (Int64.repr n))
  | _ => None
  end
.

Definition make_smt_bool (b : bool) : smt_expr :=
  match b with
  | true => SMT_Const_I1 one
  | false => SMT_Const_I1 zero
  end
.
