From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE.Numeric Require Import Integers.

(*
Definition array_model 
From SE Require Import Maps.
Definition smt_model := total_map nat.
Definition default_model := empty_map 0
*)

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
  | SMT_ITE (c e1 e2 : smt_expr)
  | SMT_Not (e : smt_expr)
  | SMT_Concat (e1 e2 : smt_expr)
  | SMT_Extract (e : smt_expr) (o w : nat)
  | SMT_Select (a : smt_array) (e : smt_expr)
  with smt_array : Type :=
    | SMT_Array (x : string)
    | SMT_Store (a : smt_array) (i e : smt_expr)
.

Inductive smt_sort : Type :=
  | Sort_BV1
  | Sort_BV8
  | Sort_BV16
  | Sort_BV32
  | Sort_BV64
  | Sort_Array
.

Module Symbol.
Inductive symbol : Type :=
  | Symbol_BV (s : string)
  | Symbol_Array (s : string)
.

(* TODO: use a module type / class *)
Definition symbol_eqb (x y : symbol) : bool :=
  match x, y with
  | Symbol_BV s1, Symbol_BV s2 => String.eqb s1 s2
  | Symbol_Array s1, Symbol_Array s2 => String.eqb s1 s2
  | _, _ => false
  end
.

Lemma symbol_eqb_refl :
  forall x, symbol_eqb x x = true.
Proof.
Admitted.

Lemma symbol_eqb_eq :
  forall x y, symbol_eqb x y = true <-> x = y.
Proof.
Admitted.

Lemma symbol_eqb_neq :
  forall x y, symbol_eqb x y = false <-> x <> y.
Proof.
Admitted.

Module End.

Definition array_model := Type.
