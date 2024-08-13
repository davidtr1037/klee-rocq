From Coq Require Import List.

Import ListNotations.

From SE Require Import CFG.
From SE Require Import LLVMAst.

Inductive is_supported_exp : (exp typ) -> Prop :=
  | IS_EXP_Ident : forall id,
      is_supported_exp (EXP_Ident id)
  | IS_EXP_Integer : forall x,
      is_supported_exp (EXP_Integer x)
  | IS_OP_IBinop : forall  t e1 e2,
      is_supported_exp e1 ->
      is_supported_exp e2 ->
      is_supported_exp (OP_IBinop (Add false false) t e1 e2)
.

Inductive is_supported_cmd : llvm_cmd -> Prop :=
  | IS_Phi : forall n p,
      is_supported_cmd (CMD_Phi n p)
  | IS_INSTR_Op : forall n v e,
      is_supported_exp e ->
      is_supported_cmd (CMD_Inst n (INSTR_Op v e))
  | IS_INSTR_VoidCall : forall n f args anns,
      is_supported_cmd (CMD_Inst n (INSTR_VoidCall f args anns))
  | IS_INSTR_Call : forall n v f args anns,
      is_supported_cmd (CMD_Inst n (INSTR_Call v f args anns))
  | IS_Term : forall n t,
      is_supported_cmd (CMD_Term n t)
.

Inductive is_supported_cmd_list : list llvm_cmd -> Prop :=
  | IS_CmdList : forall l,
      (forall c, In c l -> is_supported_cmd c) ->
      is_supported_cmd_list l
.

Inductive is_supported_block : llvm_block -> Prop :=
  | IS_Block : forall b,
      is_supported_cmd_list (blk_cmds b) ->
      is_supported_block b
.

Inductive is_supported_definition : llvm_definition -> Prop :=
  | IS_Definition : forall d,
      (forall b, In b (blks (df_body d)) -> is_supported_block b) ->
      is_supported_definition d
.

Inductive is_supported_module : llvm_module -> Prop :=
  | IS_Module : forall mdl,
      (forall d, In d (m_definitions mdl) -> is_supported_definition d) ->
      is_supported_module mdl
.
