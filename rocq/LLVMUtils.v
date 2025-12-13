From SE Require Import CFG.
From SE Require Import LLVMAst.

Inductive llvm_subexpr : llvm_exp -> llvm_exp -> Prop :=
  | LLVM_SubExpr_Refl : forall e, llvm_subexpr e e
  | LLVM_SubExpr_Trans : forall e1 e2 e3,
      llvm_subexpr e1 e2 -> llvm_subexpr e2 e3 -> llvm_subexpr e1 e3
  | LLVM_SubExpr_IBinop_L : forall op t e1 e2,
      llvm_subexpr e1 (OP_IBinop op t e1 e2)
  | LLVM_SubExpr_IBinop_R : forall op t e1 e2,
      llvm_subexpr e2 (OP_IBinop op t e1 e2)
  | LLVM_SubExpr_ICmp_L : forall op t e1 e2,
      llvm_subexpr e1 (OP_ICmp op t e1 e2)
  | LLVM_SubExpr_ICmp_R : forall op t e1 e2,
      llvm_subexpr e2 (OP_ICmp op t e1 e2)
  | LLVM_SubExpr_Conversion : forall conv t1 t2 e,
      llvm_subexpr e (OP_Conversion conv t1 e t2)
  | LLVM_SubExpr_Select_Cond : forall t1 e1 t2 e2 t3 e3,
      llvm_subexpr e1 (OP_Select t1 e1 t2 e2 t3 e3)
  | LLVM_SubExpr_Select_L : forall t1 e1 t2 e2 t3 e3,
      llvm_subexpr e2 (OP_Select t1 e1 t2 e2 t3 e3)
  | LLVM_SubExpr_Select_R : forall t1 e1 t2 e2 t3 e3,
      llvm_subexpr e3 (OP_Select t1 e1 t2 e2 t3 e3)
.

Inductive llvm_contains_ibinop : llvm_exp -> ibinop -> Prop :=
  | LLVM_Contains_IBinop : forall op t e1 e2,
      llvm_contains_ibinop (OP_IBinop op t e1 e2) op
  | LLVM_Contains_IBinop_SubExpr : forall op e1 e2,
      llvm_contains_ibinop e1 op ->
      llvm_subexpr e1 e2 ->
      llvm_contains_ibinop e2 op
.

(* TODO: remove *)
Inductive llvm_contains_division : llvm_exp -> Prop :=
  | LLVM_Contains_UDiv : forall exact e,
      llvm_contains_ibinop e (UDiv exact) ->
      llvm_contains_division e
.
