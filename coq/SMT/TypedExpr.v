From Coq Require Import Logic.Eqdep.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE.Numeric Require Import Integers.

From SE.Utils Require Import StringMap.

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

Inductive smt_sort : Type :=
  | Sort_BV1
  | Sort_BV8
  | Sort_BV16
  | Sort_BV32
  | Sort_BV64
.

Definition smt_sort_to_int_type (s : smt_sort) :=
  match s with
  | Sort_BV1 => int1
  | Sort_BV8 => int8
  | Sort_BV16 => int16
  | Sort_BV32 => int32
  | Sort_BV64 => int64
  end
.

Inductive typed_smt_ast : smt_sort -> Type :=
  | TypedSMT_Const :
      forall (s : smt_sort) (t : (smt_sort_to_int_type s)), typed_smt_ast s
  | TypedSMT_Var :
      forall (s : smt_sort) (x : string), typed_smt_ast s
  | TypedSMT_BinOp :
      forall (s : smt_sort) (op : smt_binop) (e1 e2 : typed_smt_ast s), typed_smt_ast s
  | TypedSMT_CmpOp :
      forall (s : smt_sort) (op : smt_cmpop) (e1 e2 : typed_smt_ast s), typed_smt_ast s
  | TypedSMT_Not :
      forall (s : smt_sort) (e : typed_smt_ast s), typed_smt_ast s
.

(* TODO: use sigT? *)
Inductive typed_smt_expr : Type :=
  | TypedSMTExpr (s : smt_sort) (ast : typed_smt_ast s)
.

Definition get_sort (e : typed_smt_expr) : smt_sort :=
  match e with
  | TypedSMTExpr sort _ => sort
  end
.

Definition get_ast (e : typed_smt_expr) : (typed_smt_ast (get_sort e)) :=
  match e with
  | TypedSMTExpr _ ast => ast
  end
.

Definition smt_true := (TypedSMTExpr Sort_BV1 (TypedSMT_Const Sort_BV1 one)).
Definition smt_false := (TypedSMTExpr Sort_BV1 (TypedSMT_Const Sort_BV1 zero)).

Definition make_smt_const (bits : positive) (n : Z) : option typed_smt_expr :=
  match bits with
  | 1%positive => Some (TypedSMTExpr Sort_BV1 (TypedSMT_Const Sort_BV1 (Int1.repr n)))
  | 8%positive => Some (TypedSMTExpr Sort_BV8 (TypedSMT_Const Sort_BV8 (Int8.repr n)))
  | 16%positive => Some (TypedSMTExpr Sort_BV16 (TypedSMT_Const Sort_BV16 (Int16.repr n)))
  | 32%positive => Some (TypedSMTExpr Sort_BV32 (TypedSMT_Const Sort_BV32 (Int32.repr n)))
  | 64%positive => Some (TypedSMTExpr Sort_BV64 (TypedSMT_Const Sort_BV64 (Int64.repr n)))
  | _ => None
  end
.

Definition make_smt_bool (b : bool) : typed_smt_expr :=
  match b with
  | true => smt_true
  | false => smt_false
  end
.

Inductive subexpr : typed_smt_expr -> typed_smt_expr -> Prop :=
  | SubExpr_Refl : forall e, subexpr e e
  | SubExpr_BinOp_L : forall e op sort (a1 a2 : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort a1) ->
      subexpr e (TypedSMTExpr sort (TypedSMT_BinOp sort op a1 a2))
  | SubExpr_BinOp_R : forall e op sort (a1 a2 : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort a2) ->
      subexpr e (TypedSMTExpr sort (TypedSMT_BinOp sort op a1 a2))
  | SubExpr_CmpOp_L : forall e op sort (a1 a2 : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort a1) ->
      subexpr e (TypedSMTExpr sort (TypedSMT_CmpOp sort op a1 a2))
  | SubExpr_CmpOp_R : forall e op sort (a1 a2 : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort a2) ->
      subexpr e (TypedSMTExpr sort (TypedSMT_CmpOp sort op a1 a2))
  | SubExpr_Not : forall e sort (a : (typed_smt_ast sort)),
      subexpr e (TypedSMTExpr sort a) ->
      subexpr e (TypedSMTExpr sort (TypedSMT_Not sort a))
.

Inductive contains_var : typed_smt_expr -> string -> Prop :=
  | ContainsVar : forall sort x e,
      subexpr (TypedSMTExpr sort (TypedSMT_Var sort x)) e -> contains_var e x
.

Lemma contains_var_binop : forall x sort op (a1 a2 : typed_smt_ast sort),
  contains_var (TypedSMTExpr sort (TypedSMT_BinOp sort op a1 a2)) x ->
  contains_var (TypedSMTExpr sort a1) x \/ contains_var (TypedSMTExpr sort a2) x.
Proof.
  intros x sort op a1 a2 Hc.
  inversion Hc; subst.
  inversion H; subst.
  {
    apply inj_pair2 in H5; subst.
    left.
    apply ContainsVar with (sort := sort0).
    assumption.
  }
  {
    apply inj_pair2 in H6; subst.
    right.
    apply ContainsVar with (sort := sort0).
    assumption.
  }
Qed.

(* TODO: add the other lemmas *)
