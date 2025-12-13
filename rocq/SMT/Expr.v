From Stdlib Require Import Logic.Eqdep.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.

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
  | Sort_BV24
  | Sort_BV32
  | Sort_BV40
  | Sort_BV48
  | Sort_BV56
  | Sort_BV64
.

Definition smt_sort_to_int_type (s : smt_sort) :=
  match s with
  | Sort_BV1 => int1
  | Sort_BV8 => int8
  | Sort_BV16 => int16
  | Sort_BV24 => int24
  | Sort_BV32 => int32
  | Sort_BV40 => int40
  | Sort_BV48 => int48
  | Sort_BV56 => int56
  | Sort_BV64 => int64
  end
.

Definition smt_sort_to_width (s : smt_sort) : positive :=
  match s with
  | Sort_BV1 => 1
  | Sort_BV8 => 8
  | Sort_BV16 => 16
  | Sort_BV24 => 24
  | Sort_BV32 => 32
  | Sort_BV40 => 40
  | Sort_BV48 => 48
  | Sort_BV56 => 56
  | Sort_BV64 => 64
  end
.

Inductive smt_ast : smt_sort -> Type :=
  | AST_Const :
      forall (s : smt_sort) (n : (smt_sort_to_int_type s)), smt_ast s
  | AST_Var :
      forall (s : smt_sort) (x : string), smt_ast s
  | AST_BinOp :
      forall (s : smt_sort) (op : smt_binop) (e1 e2 : smt_ast s), smt_ast s
  | AST_CmpOp :
      forall (s : smt_sort) (op : smt_cmpop) (e1 e2 : smt_ast s), smt_ast Sort_BV1
  | AST_Not :
      forall (s : smt_sort) (e : smt_ast s), smt_ast s
  | AST_ZExt :
      forall (s : smt_sort) (e : smt_ast s) (cast_sort : smt_sort), smt_ast cast_sort
  | AST_SExt :
      forall (s : smt_sort) (e : smt_ast s) (cast_sort : smt_sort), smt_ast cast_sort
  | AST_Extract :
      forall (s : smt_sort) (e : smt_ast s) (cast_sort : smt_sort), smt_ast cast_sort
  | AST_ITE :
      forall (s : smt_sort) (cond : smt_ast Sort_BV1) (e1 e2 : smt_ast s), smt_ast s
.

Definition smt_ast_bool := smt_ast Sort_BV1.
Definition smt_ast_true := AST_Const Sort_BV1 one.
Definition smt_ast_false := AST_Const Sort_BV1 zero.

(* TODO: use sigT? *)
Inductive smt_expr : Type :=
  | Expr (s : smt_sort) (ast : smt_ast s)
.

Definition get_sort (e : smt_expr) : smt_sort :=
  match e with
  | Expr sort _ => sort
  end
.

Definition get_ast (e : smt_expr) : (smt_ast (get_sort e)) :=
  match e with
  | Expr _ ast => ast
  end
.

Definition smt_expr_true := (Expr Sort_BV1 smt_ast_true).
Definition smt_expr_false := (Expr Sort_BV1 smt_ast_false).

Definition make_smt_ast_bool (b : bool) : smt_ast_bool :=
  match b with
  | true => smt_ast_true
  | false => smt_ast_false
  end
.

Definition make_smt_bool (b : bool) : smt_expr :=
  match b with
  | true => smt_expr_true
  | false => smt_expr_false
  end
.

Definition make_ast_const (n : Z) (s : smt_sort) : smt_ast s :=
  match s with
  | Sort_BV1 => AST_Const Sort_BV1 (Int1.repr n)
  | Sort_BV8 => AST_Const Sort_BV8 (repr n)
  | Sort_BV16 => AST_Const Sort_BV16 (repr n)
  | Sort_BV24 => AST_Const Sort_BV24 (repr n)
  | Sort_BV32 => AST_Const Sort_BV32 (repr n)
  | Sort_BV40 => AST_Const Sort_BV40 (repr n)
  | Sort_BV48 => AST_Const Sort_BV48 (repr n)
  | Sort_BV56 => AST_Const Sort_BV56 (repr n)
  | Sort_BV64 => AST_Const Sort_BV64 (repr n)
  end
.

(* TODO: make_const_smt_expr? *)
Definition make_smt_const (bits : positive) (n : Z) : option smt_expr :=
  match bits with
  | 1%positive => Some (Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr n)))
  | 8%positive => Some (Expr Sort_BV8 (AST_Const Sort_BV8 (Int8.repr n)))
  | 16%positive => Some (Expr Sort_BV16 (AST_Const Sort_BV16 (Int16.repr n)))
  | 24%positive => Some (Expr Sort_BV24 (AST_Const Sort_BV24 (Int24.repr n)))
  | 32%positive => Some (Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr n)))
  | 48%positive => Some (Expr Sort_BV48 (AST_Const Sort_BV48 (Int48.repr n)))
  | 56%positive => Some (Expr Sort_BV56 (AST_Const Sort_BV56 (Int56.repr n)))
  | 64%positive => Some (Expr Sort_BV64 (AST_Const Sort_BV64 (Int64.repr n)))
  | _ => None
  end
.

Inductive subexpr : smt_expr -> smt_expr -> Prop :=
  | SubExpr_Refl : forall e, subexpr e e
  | SubExpr_BinOp_L : forall e op sort (ast1 ast2 : (smt_ast sort)),
      subexpr e (Expr sort ast1) ->
      subexpr e (Expr sort (AST_BinOp sort op ast1 ast2))
  | SubExpr_BinOp_R : forall e op sort (ast1 ast2 : (smt_ast sort)),
      subexpr e (Expr sort ast2) ->
      subexpr e (Expr sort (AST_BinOp sort op ast1 ast2))
  | SubExpr_CmpOp_L : forall e op sort (ast1 ast2 : (smt_ast sort)),
      subexpr e (Expr sort ast1) ->
      subexpr e (Expr Sort_BV1 (AST_CmpOp sort op ast1 ast2))
  | SubExpr_CmpOp_R : forall e op sort (ast1 ast2 : (smt_ast sort)),
      subexpr e (Expr sort ast2) ->
      subexpr e (Expr Sort_BV1 (AST_CmpOp sort op ast1 ast2))
  | SubExpr_Not : forall e sort (a : (smt_ast sort)),
      subexpr e (Expr sort a) ->
      subexpr e (Expr sort (AST_Not sort a))
  | SubExpr_ZExt : forall e sort (a : (smt_ast sort)) cast_sort,
      subexpr e (Expr sort a) ->
      subexpr e (Expr cast_sort (AST_ZExt sort a cast_sort))
  | SubExpr_SExt : forall e sort (a : (smt_ast sort)) cast_sort,
      subexpr e (Expr sort a) ->
      subexpr e (Expr cast_sort (AST_SExt sort a cast_sort))
  | SubExpr_Extract : forall e sort (a : (smt_ast sort)) cast_sort,
      subexpr e (Expr sort a) ->
      subexpr e (Expr cast_sort (AST_Extract sort a cast_sort))
  | SubExpr_ITE_Cond : forall e sort cond (ast1 ast2 : (smt_ast sort)),
      subexpr e (Expr Sort_BV1 cond) ->
      subexpr e (Expr sort (AST_ITE sort cond ast1 ast2))
  | SubExpr_ITE_L : forall e sort cond (ast1 ast2 : (smt_ast sort)),
      subexpr e (Expr sort ast1) ->
      subexpr e (Expr sort (AST_ITE sort cond ast1 ast2))
  | SubExpr_ITE_R : forall e sort cond (ast1 ast2 : (smt_ast sort)),
      subexpr e (Expr sort ast2) ->
      subexpr e (Expr sort (AST_ITE sort cond ast1 ast2))
.

Inductive contains_var : smt_expr -> string -> Prop :=
  | ContainsVar : forall sort x e,
      subexpr (Expr sort (AST_Var sort x)) e -> contains_var e x
.

Lemma contains_var_binop : forall op sort (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr sort (AST_BinOp sort op ast1 ast2)) x ->
  contains_var (Expr sort ast1) x \/ contains_var (Expr sort ast2) x.
Proof.
  intros op sort ast1 ast2 x Hc.
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

Lemma contains_var_binop_intro_l : forall op sort (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr sort ast1) x ->
  contains_var (Expr sort (AST_BinOp sort op ast1 ast2)) x.
Proof.
  intros op sort ast1 ast2 x Hc.
  inversion Hc; subst.
  apply ContainsVar with (sort := sort0).
  apply SubExpr_BinOp_L.
  assumption.
Qed.

Lemma contains_var_binop_intro_r : forall op sort (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr sort ast2) x ->
  contains_var (Expr sort (AST_BinOp sort op ast1 ast2)) x.
Proof.
  intros op sort ast1 ast2 x Hc.
  inversion Hc; subst.
  apply ContainsVar with (sort := sort0).
  apply SubExpr_BinOp_R.
  assumption.
Qed.

Lemma contains_var_cmpop : forall op sort (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr Sort_BV1 (AST_CmpOp sort op ast1 ast2)) x ->
  contains_var (Expr sort ast1) x \/ contains_var (Expr sort ast2) x.
Proof.
  intros op sort ast1 ast2 x Hc.
  inversion Hc; subst.
  inversion H; subst.
  {
    apply inj_pair2 in H4; subst.
    left.
    apply ContainsVar with (sort := sort0).
    assumption.
  }
  {
    apply inj_pair2 in H5; subst.
    right.
    apply ContainsVar with (sort := sort0).
    assumption.
  }
Qed.

Lemma contains_var_cmpop_intro_l : forall op sort (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr sort ast1) x ->
  contains_var (Expr Sort_BV1 (AST_CmpOp sort op ast1 ast2)) x.
Proof.
  intros op sort ast1 ast2 x Hc.
  inversion Hc; subst.
  apply ContainsVar with (sort := sort0).
  apply SubExpr_CmpOp_L.
  assumption.
Qed.

Lemma contains_var_cmpop_intro_r : forall op sort (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr sort ast2) x ->
  contains_var (Expr Sort_BV1 (AST_CmpOp sort op ast1 ast2)) x.
Proof.
  intros op sort ast1 ast2 x Hc.
  inversion Hc; subst.
  apply ContainsVar with (sort := sort0).
  apply SubExpr_CmpOp_R.
  assumption.
Qed.

Lemma contains_var_not : forall sort (ast : smt_ast sort) x,
  contains_var (Expr sort (AST_Not sort ast)) x ->
  contains_var (Expr sort ast) x.
Proof.
  intros sort ast x Hc.
  inversion Hc; subst.
  inversion H; subst.
  apply inj_pair2 in H4; subst.
  apply ContainsVar with (sort := sort0).
  assumption.
Qed.

Lemma contains_var_not_intro : forall sort (ast : smt_ast sort) x,
  contains_var (Expr sort ast) x ->
  contains_var (Expr sort (AST_Not sort ast)) x.
Proof.
  intros sort ast x Hc.
  inversion Hc; subst.
  apply ContainsVar with (sort := sort0).
  apply SubExpr_Not.
  assumption.
Qed.

Lemma contains_var_zext : forall sort (ast : smt_ast sort) cast_sort x,
  contains_var (Expr cast_sort (AST_ZExt sort ast cast_sort)) x ->
  contains_var (Expr sort ast) x.
Proof.
  intros sort ast cast_sort x Hc.
  inversion Hc; subst.
  inversion H; subst.
  apply inj_pair2 in H4; subst.
  apply ContainsVar with (sort := sort0).
  assumption.
Qed.

Lemma contains_var_zext_intro : forall sort (ast : smt_ast sort) cast_sort x,
  contains_var (Expr sort ast) x ->
  contains_var (Expr cast_sort (AST_ZExt sort ast cast_sort)) x.
Proof.
  intros sort ast cast_sort x Hc.
  inversion Hc; subst.
  apply ContainsVar with (sort := sort0).
  apply SubExpr_ZExt.
  assumption.
Qed.

Lemma contains_var_sext : forall sort (ast : smt_ast sort) cast_sort x,
  contains_var (Expr cast_sort (AST_SExt sort ast cast_sort)) x ->
  contains_var (Expr sort ast) x.
Proof.
  intros sort ast cast_sort x Hc.
  inversion Hc; subst.
  inversion H; subst.
  apply inj_pair2 in H4; subst.
  apply ContainsVar with (sort := sort0).
  assumption.
Qed.

Lemma contains_var_sext_intro : forall sort (ast : smt_ast sort) cast_sort x,
  contains_var (Expr sort ast) x ->
  contains_var (Expr cast_sort (AST_SExt sort ast cast_sort)) x.
Proof.
  intros sort ast cast_sort x Hc.
  inversion Hc; subst.
  apply ContainsVar with (sort := sort0).
  apply SubExpr_SExt.
  assumption.
Qed.

Lemma contains_var_extract : forall sort (ast : smt_ast sort) cast_sort x,
  contains_var (Expr cast_sort (AST_Extract sort ast cast_sort)) x ->
  contains_var (Expr sort ast) x.
Proof.
  intros sort ast cast_sort x Hc.
  inversion Hc; subst.
  inversion H; subst.
  apply inj_pair2 in H4; subst.
  apply ContainsVar with (sort := sort0).
  assumption.
Qed.

Lemma contains_var_extract_intro : forall sort (ast : smt_ast sort) cast_sort x,
  contains_var (Expr sort ast) x ->
  contains_var (Expr cast_sort (AST_Extract sort ast cast_sort)) x.
Proof.
  intros sort ast cast_sort x Hc.
  inversion Hc; subst.
  apply ContainsVar with (sort := sort0).
  apply SubExpr_Extract.
  assumption.
Qed.

Lemma contains_var_ite : forall sort cond (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr sort (AST_ITE sort cond ast1 ast2)) x ->
  (contains_var (Expr Sort_BV1 cond) x \/ contains_var (Expr sort ast1) x \/ contains_var (Expr sort ast2) x).
Proof.
  intros sort cond ast1 ast2 x Hc.
  inversion Hc; subst.
  inversion H; subst.
  {
    apply inj_pair2 in H5; subst.
    apply inj_pair2 in H6; subst.
    left.
    eapply ContainsVar.
    eassumption.
  }
  {
    apply inj_pair2 in H5; subst.
    apply inj_pair2 in H6; subst.
    right. left.
    eapply ContainsVar.
    eassumption.
  }
  {
    apply inj_pair2 in H5; subst.
    apply inj_pair2 in H6; subst.
    right. right.
    eapply ContainsVar.
    eassumption.
  }
Qed.

Lemma contains_var_ite_intro_cond : forall sort cond (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr Sort_BV1 cond) x ->
  contains_var (Expr sort (AST_ITE sort cond ast1 ast2)) x.
Proof.
  intros sort cond ast1 ast2 x Hc.
  inversion Hc; subst.
  eapply ContainsVar.
  apply SubExpr_ITE_Cond.
  eassumption.
Qed.

Lemma contains_var_ite_intro_l : forall sort cond (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr sort ast1) x ->
  contains_var (Expr sort (AST_ITE sort cond ast1 ast2)) x.
Proof.
  intros sort cond ast1 ast2 x Hc.
  inversion Hc; subst.
  eapply ContainsVar.
  apply SubExpr_ITE_L.
  eassumption.
Qed.

Lemma contains_var_ite_intro_r : forall sort cond (ast1 ast2 : smt_ast sort) x,
  contains_var (Expr sort ast2) x ->
  contains_var (Expr sort (AST_ITE sort cond ast1 ast2)) x.
Proof.
  intros sort cond ast1 ast2 x Hc.
  inversion Hc; subst.
  eapply ContainsVar.
  apply SubExpr_ITE_R.
  eassumption.
Qed.
