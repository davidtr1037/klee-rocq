From Coq Require Import Strings.String.

From SE Require Import BitVectors.
From SE Require Import DynamicValue.
(* TODO: avoid this dependency *)
From SE Require Import LLVMAst.
(* TODO: is needed? *)
From SE.Numeric Require Import Integers.
From SE.SMT Require Import Expr.
From SE.Utils Require Import StringMap.

Inductive symbol : Type :=
  | Symbol_BV (s : string)
  | Symbol_Array (s : string)
.

Record smt_model := mk_smt_model {
  bv_model : total_map dynamic_int;
}.

(* TODO: define default model *)

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
  | SMT_Var x => Some ((bv_model m) x)
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
  | SMT_ZExt e w => None
  | SMT_SExt e w => None
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

Lemma subexpr_non_interference : forall e x m n,
  (~ subexpr (SMT_Var x) e) -> smt_eval m e = smt_eval (mk_smt_model (x !-> n; bv_model m)) e.
Proof.
  intros e x m n H.
  induction e; simpl; try reflexivity.
  {
    destruct (x =? x0)%string eqn:E.
    {
      rewrite String.eqb_eq in E.
      subst.
      destruct H.
      apply SubExpr_Refl.
    }
    {
      rewrite String.eqb_neq in E.
      rewrite update_map_neq.
      { reflexivity. }
      { assumption. }
    }
  }
  { (* SMT_BinOp *)
    assert(L1 : ~ subexpr (SMT_Var x) e1).
    { intros Hse. apply H. apply SubExpr_BinOp_L. assumption. }
    assert(L2 : ~ subexpr (SMT_Var x) e2).
    { intros Hse. apply H. apply SubExpr_BinOp_R. assumption. }
    apply IHe1 in L1.
    apply IHe2 in L2.
    rewrite L1, L2.
    reflexivity.
  }
  { (* SMT_CmpOp *)
    assert(L1 : ~ subexpr (SMT_Var x) e1).
    { intros Hse. apply H. apply SubExpr_CmpOp_L. assumption. }
    assert(L2 : ~ subexpr (SMT_Var x) e2).
    { intros Hse. apply H. apply SubExpr_CmpOp_R. assumption. }
    apply IHe1 in L1.
    apply IHe2 in L2.
    rewrite L1, L2.
    reflexivity.
  }
  {
    assert(L1 : ~ subexpr (SMT_Var x) e1).
    { intros Hse. apply H. apply SubExpr_ITE_Cond. assumption. }
    assert(L2 : ~ subexpr (SMT_Var x) e2).
    { intros Hse. apply H. apply SubExpr_ITE_L. assumption. }
    assert(L3 : ~ subexpr (SMT_Var x) e3).
    { intros Hse. apply H. apply SubExpr_ITE_R. assumption. }
    apply IHe1 in L1.
    apply IHe2 in L2.
    apply IHe3 in L3.
    rewrite L1, L2, L3.
    reflexivity.
  }
  {
    assert(L : ~ subexpr (SMT_Var x) e).
    { intros Hse. apply H. apply SubExpr_Not. assumption. }
    apply IHe in L.
    rewrite L.
    reflexivity.
  }
Qed.

Inductive equiv_smt_expr : smt_expr -> smt_expr -> Prop :=
  | EquivSMTExpr : forall e1 e2,
      (forall m, exists dv, smt_eval m e1 = Some dv /\ smt_eval m e2 = Some dv) ->
      equiv_smt_expr e1 e2
.
