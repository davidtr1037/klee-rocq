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
.

Definition SMT_True := SMT_Const_I1 one.
Definition SMT_False := SMT_Const_I1 zero.

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

Inductive subexpr : smt_expr -> smt_expr -> Prop :=
  | SubExpr_Refl : forall e, subexpr e e
  | SubExpr_BinOp_L : forall e op e1 e2,
      subexpr e e1 -> subexpr e (SMT_BinOp op e1 e2)
  | SubExpr_BinOp_R : forall e op e1 e2,
      subexpr e e2 -> subexpr e (SMT_BinOp op e1 e2)
  | SubExpr_CmpOp_L : forall e op e1 e2,
      subexpr e e1 -> subexpr e (SMT_CmpOp op e1 e2)
  | SubExpr_CmpOp_R : forall e op e1 e2,
      subexpr e e2 -> subexpr e (SMT_CmpOp op e1 e2)
  | SubExpr_ZExt : forall e e1 w,
      subexpr e e1 -> subexpr e (SMT_ZExt e1 w)
  | SubExpr_SExt : forall e e1 w,
      subexpr e e1 -> subexpr e (SMT_SExt e1 w)
  | SubExpr_ITE_Cond : forall e e1 e2 e3,
      subexpr e e1 -> subexpr e (SMT_ITE e1 e2 e3)
  | SubExpr_ITE_L : forall e e1 e2 e3,
      subexpr e e2 -> subexpr e (SMT_ITE e1 e2 e3)
  | SubExpr_ITE_R : forall e e1 e2 e3,
      subexpr e e3 -> subexpr e (SMT_ITE e1 e2 e3)
  | SubExpr_Not : forall e e1,
      subexpr e e1 -> subexpr e (SMT_Not e1)
  | SubExpr_Concat_L : forall e e1 e2,
      subexpr e e1 -> subexpr e (SMT_Concat e1 e2)
  | SubExpr_Concat_R : forall e e1 e2,
      subexpr e e2 -> subexpr e (SMT_Concat e1 e2)
  | SubExpr_Extract : forall e e1 i w,
      subexpr e e1 -> subexpr e (SMT_Extract e1 i w)
.

Inductive contains_var : smt_expr -> string -> Prop :=
  | ContainsVar_I1 : forall x e,
      subexpr (SMT_Var_I1 x) e -> contains_var e x
  | ContainsVar_I8 : forall x e,
      subexpr (SMT_Var_I8 x) e -> contains_var e x
  | ContainsVar_I16 : forall x e,
      subexpr (SMT_Var_I16 x) e -> contains_var e x
  | ContainsVar_I32 : forall x e,
      subexpr (SMT_Var_I32 x) e -> contains_var e x
  | ContainsVar_I64 : forall x e,
      subexpr (SMT_Var_I64 x) e -> contains_var e x
.

Lemma contains_var_binop : forall x op e1 e2,
  contains_var (SMT_BinOp op e1 e2) x ->
  contains_var e1 x \/ contains_var e2 x.
Proof.
  intros x op e1 e2 Hc.
  inversion Hc; subst; (
    inversion H; subst;
    [
      left;
      try (apply ContainsVar_I1; assumption);
      try (apply ContainsVar_I8; assumption);
      try (apply ContainsVar_I16; assumption);
      try (apply ContainsVar_I32; assumption);
      try (apply ContainsVar_I64; assumption) |
      right;
      try (apply ContainsVar_I1; assumption);
      try (apply ContainsVar_I8; assumption);
      try (apply ContainsVar_I16; assumption);
      try (apply ContainsVar_I32; assumption);
      try (apply ContainsVar_I64; assumption)
    ]
  ).
Qed.

Lemma contains_var_binop_intro_l : forall x op e1 e2,
  contains_var e1 x -> contains_var (SMT_BinOp op e1 e2) x.
Proof.
  intros x op e1 e2 Hc.
  inversion Hc; subst.
  { apply ContainsVar_I1. apply SubExpr_BinOp_L. assumption. }
  { apply ContainsVar_I8. apply SubExpr_BinOp_L. assumption. }
  { apply ContainsVar_I16. apply SubExpr_BinOp_L. assumption. }
  { apply ContainsVar_I32. apply SubExpr_BinOp_L. assumption. }
  { apply ContainsVar_I64. apply SubExpr_BinOp_L. assumption. }
Qed.

Lemma contains_var_binop_intro_r : forall x op e1 e2,
  contains_var e2 x -> contains_var (SMT_BinOp op e1 e2) x.
Proof.
  intros x op e1 e2 Hc.
  inversion Hc; subst.
  { apply ContainsVar_I1. apply SubExpr_BinOp_R. assumption. }
  { apply ContainsVar_I8. apply SubExpr_BinOp_R. assumption. }
  { apply ContainsVar_I16. apply SubExpr_BinOp_R. assumption. }
  { apply ContainsVar_I32. apply SubExpr_BinOp_R. assumption. }
  { apply ContainsVar_I64. apply SubExpr_BinOp_R. assumption. }
Qed.

Lemma contains_var_cmpop : forall x op e1 e2,
  contains_var (SMT_CmpOp op e1 e2) x ->
  contains_var e1 x \/ contains_var e2 x.
Proof.
  intros x op e1 e2 Hc.
  inversion Hc; subst; (
    inversion H; subst;
    [
      left;
      try (apply ContainsVar_I1; assumption);
      try (apply ContainsVar_I8; assumption);
      try (apply ContainsVar_I16; assumption);
      try (apply ContainsVar_I32; assumption);
      try (apply ContainsVar_I64; assumption) |
      right;
      try (apply ContainsVar_I1; assumption);
      try (apply ContainsVar_I8; assumption);
      try (apply ContainsVar_I16; assumption);
      try (apply ContainsVar_I32; assumption);
      try (apply ContainsVar_I64; assumption)
    ]
  ).
Qed.

Lemma contains_var_cmpop_intro_l : forall x op e1 e2,
  contains_var e1 x -> contains_var (SMT_CmpOp op e1 e2) x.
Proof.
  intros x op e1 e2 Hc.
  inversion Hc; subst.
  { apply ContainsVar_I1. apply SubExpr_CmpOp_L. assumption. }
  { apply ContainsVar_I8. apply SubExpr_CmpOp_L. assumption. }
  { apply ContainsVar_I16. apply SubExpr_CmpOp_L. assumption. }
  { apply ContainsVar_I32. apply SubExpr_CmpOp_L. assumption. }
  { apply ContainsVar_I64. apply SubExpr_CmpOp_L. assumption. }
Qed.

Lemma contains_var_cmpop_intro_r : forall x op e1 e2,
  contains_var e2 x -> contains_var (SMT_CmpOp op e1 e2) x.
Proof.
  intros x op e1 e2 Hc.
  inversion Hc; subst.
  { apply ContainsVar_I1. apply SubExpr_CmpOp_R. assumption. }
  { apply ContainsVar_I8. apply SubExpr_CmpOp_R. assumption. }
  { apply ContainsVar_I16. apply SubExpr_CmpOp_R. assumption. }
  { apply ContainsVar_I32. apply SubExpr_CmpOp_R. assumption. }
  { apply ContainsVar_I64. apply SubExpr_CmpOp_R. assumption. }
Qed.

Lemma contains_var_not : forall x e,
  contains_var (SMT_Not e) x -> contains_var e x.
Proof.
  intros x e Hc.
  inversion Hc; subst; (
    inversion H; subst;
    try (apply ContainsVar_I1; assumption);
    try (apply ContainsVar_I8; assumption);
    try (apply ContainsVar_I16; assumption);
    try (apply ContainsVar_I32; assumption);
    try (apply ContainsVar_I64; assumption)
  ).
Qed.

Lemma contains_var_not_inverse : forall x e,
  contains_var e x -> contains_var (SMT_Not e) x.
Proof.
  intros x e Hc.
  inversion Hc; subst.
  { apply ContainsVar_I1. apply SubExpr_Not. assumption. }
  { apply ContainsVar_I8. apply SubExpr_Not. assumption. }
  { apply ContainsVar_I16. apply SubExpr_Not. assumption. }
  { apply ContainsVar_I32. apply SubExpr_Not. assumption. }
  { apply ContainsVar_I64. apply SubExpr_Not. assumption. }
Qed.

Lemma contains_var_extract : forall x e i w,
  contains_var (SMT_Extract e i w) x -> contains_var e x.
Proof.
  intros x e i w Hc.
  inversion Hc; subst; (
    inversion H; subst;
    try (apply ContainsVar_I1; assumption);
    try (apply ContainsVar_I8; assumption);
    try (apply ContainsVar_I16; assumption);
    try (apply ContainsVar_I32; assumption);
    try (apply ContainsVar_I64; assumption)
  ).
Qed.

Lemma contains_var_zext : forall x e w,
  contains_var (SMT_ZExt e w) x -> contains_var e x.
Proof.
  intros x e w Hc.
  inversion Hc; subst; (
    inversion H; subst;
    try (apply ContainsVar_I1; assumption);
    try (apply ContainsVar_I8; assumption);
    try (apply ContainsVar_I16; assumption);
    try (apply ContainsVar_I32; assumption);
    try (apply ContainsVar_I64; assumption)
  ).
Qed.

Lemma contains_var_sext : forall x e w,
  contains_var (SMT_SExt e w) x -> contains_var e x.
Proof.
  intros x e w Hc.
  inversion Hc; subst; (
    inversion H; subst;
    try (apply ContainsVar_I1; assumption);
    try (apply ContainsVar_I8; assumption);
    try (apply ContainsVar_I16; assumption);
    try (apply ContainsVar_I32; assumption);
    try (apply ContainsVar_I64; assumption)
  ).
Qed.

Lemma contains_var_ite_intro_cond : forall x cond e1 e2,
  contains_var cond x -> contains_var (SMT_ITE cond e1 e2) x.
Proof.
  intros x cond e1 e2 Hc.
  inversion Hc; subst.
  { apply ContainsVar_I1. apply SubExpr_ITE_Cond. assumption. }
  { apply ContainsVar_I8. apply SubExpr_ITE_Cond. assumption. }
  { apply ContainsVar_I16. apply SubExpr_ITE_Cond. assumption. }
  { apply ContainsVar_I32. apply SubExpr_ITE_Cond. assumption. }
  { apply ContainsVar_I64. apply SubExpr_ITE_Cond. assumption. }
Qed.

Lemma contains_var_ite_intro_l : forall x cond e1 e2,
  contains_var e1 x -> contains_var (SMT_ITE cond e1 e2) x.
Proof.
  intros x cond e1 e2 Hc.
  inversion Hc; subst.
  { apply ContainsVar_I1. apply SubExpr_ITE_L. assumption. }
  { apply ContainsVar_I8. apply SubExpr_ITE_L. assumption. }
  { apply ContainsVar_I16. apply SubExpr_ITE_L. assumption. }
  { apply ContainsVar_I32. apply SubExpr_ITE_L. assumption. }
  { apply ContainsVar_I64. apply SubExpr_ITE_L. assumption. }
Qed.

Lemma contains_var_ite_intro_r : forall x cond e1 e2,
  contains_var e2 x -> contains_var (SMT_ITE cond e1 e2) x.
Proof.
  intros x cond e1 e2 Hc.
  inversion Hc; subst.
  { apply ContainsVar_I1. apply SubExpr_ITE_R. assumption. }
  { apply ContainsVar_I8. apply SubExpr_ITE_R. assumption. }
  { apply ContainsVar_I16. apply SubExpr_ITE_R. assumption. }
  { apply ContainsVar_I32. apply SubExpr_ITE_R. assumption. }
  { apply ContainsVar_I64. apply SubExpr_ITE_R. assumption. }
Qed.
