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

Inductive is_supported_function_arg : function_arg -> Prop :=
  | IS_FunctionArg : forall t e attrs,
      is_supported_exp e ->
      is_supported_function_arg ((t, e), attrs)
.

Inductive is_supported_cmd : llvm_cmd -> Prop :=
  | IS_Phi : forall n v t args,
      (forall bid e, In (bid, e) args -> is_supported_exp e) ->
      is_supported_cmd (CMD_Phi n (Phi v t args))
  | IS_INSTR_Op : forall n v e,
      is_supported_exp e ->
      is_supported_cmd (CMD_Inst n (INSTR_Op v e))
  | IS_INSTR_VoidCall : forall n f args anns,
      (forall arg, In arg args -> is_supported_function_arg arg) ->
      is_supported_cmd (CMD_Inst n (INSTR_VoidCall f args anns))
  | IS_INSTR_Call : forall n v f args anns,
      (forall arg, In arg args -> is_supported_function_arg arg) ->
      is_supported_cmd (CMD_Inst n (INSTR_Call v f args anns))
  | IS_Term_Ret : forall n t e,
      is_supported_exp e ->
      is_supported_cmd (CMD_Term n (TERM_Ret (t, e)))
  | IS_Term_RetVoid : forall n,
      is_supported_cmd (CMD_Term n TERM_RetVoid)
  | IS_Term_Br : forall n t e bid1 bid2,
      is_supported_exp e ->
      is_supported_cmd (CMD_Term n (TERM_Br (t, e) bid1 bid2))
  | IS_Term_UnconditionalBr : forall n bid,
      is_supported_cmd (CMD_Term n (TERM_UnconditionalBr bid))
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

Inductive is_supported_global : llvm_global -> Prop :=
  | IS_Global : forall (g : llvm_global) (e : exp typ),
      (g_exp g) = Some e ->
      is_supported_exp e ->
      is_supported_global g
.

Inductive is_supported_module : llvm_module -> Prop :=
  | IS_Module : forall mdl,
      (forall g, In g (m_globals mdl) -> is_supported_global g) ->
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

(* TODO: fix init_state / init_sym_state *)
Lemma init_state_supported : forall mdl d s,
  is_supported_module mdl ->
  init_state mdl d = Some s -> is_supported_state s.
Proof.
  intros mdl d s Hism Heq.
  unfold init_state in Heq.
  destruct (build_inst_counter mdl d) as [c_ic | ] eqn:Ec_ic; try discriminate Heq.
  destruct (entry_block d) as [c_b | ] eqn:Ec_b; try discriminate Heq.
  destruct (blk_cmds c_b) as [ | c_cmd c_cmds ] eqn:Ec_cs; try discriminate Heq.
  admit.
Admitted.

Lemma step_supported : forall mdl s s',
  is_supported_module mdl ->
  step s s' ->
  is_supported_state s ->
  is_supported_state s'.
Proof.
  intros mdl s s' Hism Hs His.
  inversion Hs; subst; inversion His; subst.
  {
    inversion H9; subst.
    apply IS_State.
    { apply (H0 c). apply in_eq. }
    {
      apply IS_CmdList.
      intros c' Hin.
      apply H0.
      apply in_cons.
      assumption.
    }
  }
  { admit. } (* phi *)
Admitted.

Lemma multi_step_supported : forall mdl s s',
  is_supported_module mdl ->
  multi_step s s' ->
  is_supported_state s ->
  is_supported_state s'.
Proof.
  intros mdl s s' Hism Hms His.
  induction Hms as [s s' | s s' s''].
  { apply (step_supported mdl s s'); assumption.  }
  {
    apply IHHms in His.
    apply (step_supported mdl s' s''); assumption.
  }
Qed.
