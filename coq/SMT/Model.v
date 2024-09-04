From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE Require Import DynamicValue.

From SE.Numeric Require Import Integers.

From SE.SMT Require Import Expr.

From SE.Utils Require Import StringMap.
From SE.Utils Require Import Util.

Inductive symbol : Type :=
  | Symbol_BV (s : string)
  | Symbol_Array (s : string)
.

Record smt_model := mk_smt_model {
  bv_model : total_map dynamic_int;
}.

Definition default_model := mk_smt_model (empty_map di_false).

Definition smt_eval_binop_generic {Int} `{VInt Int} (op : smt_binop) (x y : Int) : dynamic_int :=
  match op with
  | SMT_Add => to_dint (add x y)
  | SMT_Sub => to_dint (sub x y)
  | SMT_Mul => to_dint (mul x y)
  | SMT_UDiv => to_dint (divu x y)
  | SMT_SDiv => to_dint (divs x y)
  | SMT_URem => to_dint (modu x y)
  | SMT_SRem => to_dint (mods x y)
  | SMT_And => to_dint (and x y)
  | SMT_Or => to_dint (or x y)
  | SMT_Xor => to_dint (xor x y)
  | SMT_Shl => to_dint (shl x y)
  | SMT_LShr => to_dint (shru x y)
  | SMT_AShr => to_dint (shr x y)
  end
.

Definition smt_eval_binop (op : smt_binop) (v1 v2 : dynamic_int) : option dynamic_int :=
  match (v1, v2) with
  | (DI_I1 n1, DI_I1 n2)
  | (DI_I8 n1, DI_I8 n2)
  | (DI_I16 n1, DI_I16 n2)
  | (DI_I32 n1, DI_I32 n2)
  | (DI_I64 n1, DI_I64 n2) => Some (smt_eval_binop_generic op n1 n2)
  | _ => None
  end
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

Definition smt_eval_cmpop (op : smt_cmpop) (v1 v2 : dynamic_int) : option dynamic_int :=
  match (v1, v2) with
  | (DI_I1 n1, DI_I1 n2)
  | (DI_I8 n1, DI_I8 n2)
  | (DI_I16 n1, DI_I16 n2)
  | (DI_I32 n1, DI_I32 n2)
  | (DI_I64 n1, DI_I64 n2) =>
      if (smt_eval_cmpop_generic op n1 n2) then
        Some di_true
      else
        Some di_false
  | _ => None
  end
.

(* TODO: implement *)
(* TODO: use a single constructor SMT_Const (with dynamic_int)? *)
Fixpoint smt_eval (m : smt_model) (e : smt_expr) : option dynamic_int :=
  match e with
  | SMT_Const_I1 n => Some (DI_I1 n)
  | SMT_Const_I8 n => Some (DI_I8 n)
  | SMT_Const_I16 n => Some (DI_I16 n)
  | SMT_Const_I32 n => Some (DI_I32 n)
  | SMT_Const_I64 n => Some (DI_I64 n)
  | SMT_Var_I1 x =>
      match ((bv_model m) x) with
      | DI_I1 n => Some (DI_I1 n)
      | _ => None
      end
  | SMT_Var_I8 x =>
      match ((bv_model m) x) with
      | DI_I8 n => Some (DI_I8 n)
      | _ => None
      end
  | SMT_Var_I16 x =>
      match ((bv_model m) x) with
      | DI_I16 n => Some (DI_I16 n)
      | _ => None
      end
  | SMT_Var_I32 x =>
      match ((bv_model m) x) with
      | DI_I32 n => Some (DI_I32 n)
      | _ => None
      end
  | SMT_Var_I64 x =>
      match ((bv_model m) x) with
      | DI_I64 n => Some (DI_I64 n)
      | _ => None
      end
  | SMT_BinOp op e1 e2 =>
      match (smt_eval m e1), (smt_eval m e2) with
      | Some di1, Some di2 => smt_eval_binop op di1 di2
      | _, _ => None
      end
  | SMT_CmpOp op e1 e2 =>
      match (smt_eval m e1), (smt_eval m e2) with
      | Some di1, Some di2 => smt_eval_cmpop op di1 di2
      | _, _ => None
      end
  | SMT_ZExt e w => None (* TODO: ... *)
  | SMT_SExt e w => None (* TODO: ... *)
  | SMT_ITE e1 e2 e3 =>
      match (smt_eval m e1) with
      | Some (DI_I1 b) =>
          if eq b one then
            smt_eval m e2
          else
            smt_eval m e3
      | _ => None
      end
  (* TODO: overcome decreasing issue? *)
  | SMT_Not e =>
      match (smt_eval m e) with
      | Some di => smt_eval_cmpop SMT_Eq di di_false
      | _ => None
      end
  | SMT_Concat e1 e2 => None
  | SMT_Extract e i w => None
  end
.

Definition sat_via (e : smt_expr) (m : smt_model) :=
  smt_eval m e = Some di_true
.

Definition sat (e : smt_expr) :=
  exists (m : smt_model), sat_via e m
.

Definition unsat (e : smt_expr) := ~ sat e.

Lemma unsat_and : forall e1 e2,
  unsat e1 ->
  unsat (SMT_BinOp SMT_And e1 e2).
Proof.
  intros e1 e2 Hu.
  unfold unsat in *.
  intros Hsat.
  apply Hu.
  unfold sat in *.
  destruct Hsat as [m Hsat].
  exists m.
  unfold sat_via in *.
  simpl in Hsat.
  destruct (smt_eval m e1) as [di1 | ] eqn:E1, (smt_eval m e2) as [di2 | ] eqn:E2; try (
    discriminate Hsat
  ).
  {
    destruct di1, di2;
    try (
      unfold smt_eval_binop in Hsat;
      discriminate Hsat
    ).
    {
      rename n into n1, n0 into n2.
      unfold smt_eval_binop in Hsat.
      unfold smt_eval_binop_generic in Hsat.
      apply injection_some in Hsat.
      apply f_equal.
      apply (int1_and_true n1 n2).
      assumption.
    }
  }
Qed.

Lemma subexpr_non_interference : forall e x m n,
  (~ contains_var e x ) -> smt_eval m e = smt_eval (mk_smt_model (x !-> n; bv_model m)) e.
Proof.
  intros e x m n H.
  induction e; simpl; try reflexivity; try (
    destruct (x =? x0)%string eqn:E;
    [
      rewrite String.eqb_eq in E;
      subst;
      destruct H;
      try (apply ContainsVar_I1; apply SubExpr_Refl);
      try (apply ContainsVar_I8; apply SubExpr_Refl);
      try (apply ContainsVar_I16; apply SubExpr_Refl);
      try (apply ContainsVar_I32; apply SubExpr_Refl);
      try (apply ContainsVar_I64; apply SubExpr_Refl);
      apply SubExpr_Refl |
      rewrite String.eqb_neq in E;
      rewrite update_map_neq;
      [
        reflexivity |
        assumption
      ]
    ]
  ).
  {
    assert(L1 : ~ contains_var e1 x).
    { intros Hse. apply H. apply contains_var_binop_l. assumption. }
    assert(L2 : ~ contains_var e2 x).
    { intros Hse. apply H. apply contains_var_binop_r. assumption. }
    apply IHe1 in L1.
    apply IHe2 in L2.
    rewrite L1, L2.
    reflexivity.
  }
  {
    assert(L1 : ~ contains_var e1 x).
    { intros Hse. apply H. apply contains_var_cmpop_l. assumption. }
    assert(L2 : ~ contains_var e2 x).
    { intros Hse. apply H. apply contains_var_cmpop_r. assumption. }
    apply IHe1 in L1.
    apply IHe2 in L2.
    rewrite L1, L2.
    reflexivity.
  }
  {
    assert(L1 : ~ contains_var e1 x).
    { intros Hse. apply H. apply contains_var_ite_cond. assumption. }
    assert(L2 : ~ contains_var e2 x).
    { intros Hse. apply H. apply contains_var_ite_l. assumption. }
    assert(L3 : ~ contains_var e3 x).
    { intros Hse. apply H. apply contains_var_ite_r. assumption. }
    apply IHe1 in L1.
    apply IHe2 in L2.
    apply IHe3 in L3.
    rewrite L1, L2, L3.
    reflexivity.
  }
  {
    assert(L : ~ contains_var e x).
    { intros Hse. apply H. apply contains_var_not_inverse. assumption. }
    apply IHe in L.
    rewrite L.
    reflexivity.
  }
Qed.

Inductive equiv_smt_expr : smt_expr -> smt_expr -> Prop :=
  | EquivSMTExpr : forall e1 e2,
      (forall m,
        (smt_eval m e1 = None /\ smt_eval m e2 = None) \/
        (exists dv, smt_eval m e1 = Some dv /\ smt_eval m e2 = Some dv)
      ) -> equiv_smt_expr e1 e2
.

Lemma equiv_smt_expr_refl : forall e, equiv_smt_expr e e.
Proof.
  intros e.
  apply EquivSMTExpr.
  intros m.
  destruct (smt_eval m e) as [se | ] eqn:E.
  {
    right.
    exists se.
    split; reflexivity.
  }
  {
    left.
    split; reflexivity.
  }
Qed.

Lemma equiv_smt_expr_symmetry : forall e1 e2,
  equiv_smt_expr e1 e2 -> equiv_smt_expr e2 e1.
Proof.
  intros s1 s2 Heq.
  inversion Heq; subst.
  apply EquivSMTExpr.
  intros m.
  specialize (H m).
  destruct H as [[H_1 H_2]| H].
  {
    left.
    split; assumption.
  }
  {
    destruct H as [dv [H_1 H_2]].
    right.
    exists dv.
    split; assumption.
  }
Qed.

Lemma equiv_smt_expr_transitivity : forall e1 e2 e3,
  equiv_smt_expr e1 e2 -> equiv_smt_expr e2 e3 -> equiv_smt_expr e1 e3.
Proof.
  intros e1 e2 e3 Heq1 Heq2.
  inversion Heq1; subst.
  inversion Heq2; subst.
  apply EquivSMTExpr.
  intros m.
  specialize (H m).
  specialize (H0 m).
  destruct H as [[H_1 H_2]| [dv1 [H_1 H_2]]].
  {
    destruct H0 as [[H0_1 H0_2]| [dv2 [H0_1 H0_2]]].
    {
      left.
      split; assumption.
    }
    { rewrite H_2 in H0_1. discriminate H0_1. }
  }
  {
    destruct H0 as [[H0_1 H0_2]| [dv2 [H0_1 H0_2]]].
    { rewrite H_2 in H0_1. discriminate H0_1. }
    {
      right.
      exists dv1.
      split.
      { assumption. }
      { rewrite H_2 in H0_1. rewrite <- H0_1 in H0_2. assumption. }
    }
  }
Qed.

Lemma equiv_smt_expr_unsat : forall e1 e2,
  equiv_smt_expr e1 e2 -> unsat e1 -> unsat e2.
Proof.
  intros e1 e2 Heq Hu.
  unfold unsat, sat in *.
  intros Hsat.
  destruct Hsat as [m Hsat].
  apply Hu.
  exists m.
  inversion Heq; subst.
  specialize (H m).
  unfold sat_via in *.
  destruct H as [H | H].
  {
    destruct H as [H_1 H_2].
    rewrite Hsat in H_2.
    discriminate H_2.
  }
  {
    destruct H as [dv [H_1 H_2]].
    rewrite Hsat in H_2.
    rewrite <- H_2 in H_1.
    assumption.
  }
Qed.

Lemma equiv_smt_expr_not : forall e1 e2,
  equiv_smt_expr e1 e2 ->
  equiv_smt_expr (SMT_Not e1) (SMT_Not e2).
Proof.
  intros e1 e2 Heq.
  inversion Heq; subst.
  apply EquivSMTExpr.
  intros m.
  specialize (H m).
  destruct H as [[H_1 H_2] | [dv [H_1 H_2]]].
  {
    left.
    simpl.
    rewrite H_1, H_2.
    split; reflexivity.
  }
  {
    simpl.
    rewrite H_1, H_2.
    destruct (smt_eval_cmpop SMT_Eq dv di_false) as [di | ] eqn:E.
    {
      right.
      exists di.
      split; reflexivity.
    }
    {
      left.
      split; reflexivity.
    }
  }
Qed.

Lemma equiv_smt_expr_binop : forall op e1 e2 e3 e4,
  equiv_smt_expr e1 e2 ->
  equiv_smt_expr e3 e4 ->
  equiv_smt_expr (SMT_BinOp op e1 e3) (SMT_BinOp op e2 e4).
Proof.
  intros op e1 e2 e3 e4 Heq1 Heq2.
  inversion Heq1; subst.
  inversion Heq2; subst.
  apply EquivSMTExpr.
  intros m.
  specialize (H m).
  specialize (H0 m).
  destruct H as [[H_1 H_2] | [di1 [H_1 H_2]]].
  {
    left.
    simpl.
    rewrite H_1, H_2.
    split; reflexivity.
  }
  {
    destruct H0 as [[H0_1 H0_2] | [di2 [H0_1 H0_2]]].
    {
      left.
      simpl.
      rewrite H_1, H_2, H0_1, H0_2.
      split; reflexivity.
    }
    {
      simpl.
      rewrite H_1, H_2, H0_1, H0_2.
      destruct (smt_eval_binop op di1 di2) as [di | ] eqn:E.
      { right. exists di. split; reflexivity. }
      { left. split; reflexivity. }
    }
  }
Qed.

Lemma equiv_smt_expr_cmpop : forall op e1 e2 e3 e4,
  equiv_smt_expr e1 e2 ->
  equiv_smt_expr e3 e4 ->
  equiv_smt_expr (SMT_CmpOp op e1 e3) (SMT_CmpOp op e2 e4).
Proof.
  intros op e1 e2 e3 e4 Heq1 Heq2.
  inversion Heq1; subst.
  inversion Heq2; subst.
  apply EquivSMTExpr.
  intros m.
  specialize (H m).
  specialize (H0 m).
  destruct H as [[H_1 H_2] | [di1 [H_1 H_2]]].
  {
    left.
    simpl.
    rewrite H_1, H_2.
    split; reflexivity.
  }
  {
    destruct H0 as [[H0_1 H0_2] | [di2 [H0_1 H0_2]]].
    {
      left.
      simpl.
      rewrite H_1, H_2, H0_1, H0_2.
      split; reflexivity.
    }
    {
      simpl.
      rewrite H_1, H_2, H0_1, H0_2.
      destruct (smt_eval_cmpop op di1 di2) as [di | ] eqn:E.
      { right. exists di. split; reflexivity. }
      { left. split; reflexivity. }
    }
  }
Qed.

(*
Definition subst_var (e : smt_expr) (x y : string) : smt_expr :=
  e
.

Inductive iso_smt_expr : smt_expr -> smt_expr -> Prop :=
  | Iso_Eq : forall e,
      iso_smt_expr e e
  | Iso_Subst : forall e1 e2 e3 x y,
      ~ subexpr (SMT_Var y) e2 ->
      e1 = (subst_var e2 x y) ->
      iso_smt_expr e2 e3 ->
      iso_smt_expr e1 e3
.
*)

Fixpoint simplify (e : smt_expr) : smt_expr :=
  match e with
  | SMT_BinOp op e1 e2 =>
    match op with
    | SMT_Add =>
      match (simplify e1), (simplify e2) with
      | SMT_Const_I1 n1, SMT_Const_I1 n2 => SMT_Const_I1 (add n1 n2)
      | SMT_Const_I8 n1, SMT_Const_I8 n2 => SMT_Const_I8 (add n1 n2)
      | SMT_Const_I16 n1, SMT_Const_I16 n2 => SMT_Const_I16 (add n1 n2)
      | SMT_Const_I32 n1, SMT_Const_I32 n2 => SMT_Const_I32 (add n1 n2)
      | SMT_Const_I64 n1, SMT_Const_I64 n2 => SMT_Const_I64 (add n1 n2)
      | _, _ => e
      end
    | _ => e
    end
  | _ => e
  end
.

Lemma equiv_smt_expr_simplify : forall e,
  equiv_smt_expr e (simplify e)
.
Proof.
Admitted.
