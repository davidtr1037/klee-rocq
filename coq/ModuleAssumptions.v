From Coq Require Import List.

Import ListNotations.

From SE Require Import CFG.
From SE Require Import Concrete.
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

Inductive is_supported_state : state -> Prop :=
  | IS_State : forall ic c cs pbid ls stk gs mdl,
      is_supported_cmd c ->
      is_supported_cmd_list cs ->
      is_supported_state
        (mk_state
          ic
          c
          cs
          pbid
          ls
          stk
          gs
          mdl
        )
.

Lemma init_state_supported : forall mdl d s,
  is_supported_module mdl ->
  init_state mdl d = Some s -> is_supported_state s.
Proof.
Admitted.

Lemma multi_step_supported : forall mdl s s',
  is_supported_module mdl ->
  multi_step s s' ->
  is_supported_state s ->
  is_supported_state s'.
Proof.
Admitted.
