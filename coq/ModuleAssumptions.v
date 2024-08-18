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

Lemma LX0 : forall mdl e d,
  find_function_by_exp mdl e = Some d ->
  In d (m_definitions mdl).
Proof.
Admitted.

Lemma LX1 : forall mdl d fid,
  find_function mdl fid = Some d ->
  In d (m_definitions mdl).
Proof.
Admitted.

Lemma LX2 : forall d bid b,
  fetch_block d bid = Some b ->
  In b (blks (df_body d)).
Proof.
Admitted.

Lemma LX3 : forall c cs,
  is_supported_cmd_list (c :: cs)  -> is_supported_cmd_list cs.
Proof.
  intros c cs H.
  apply IS_CmdList.
  intros c' Hin.
  inversion H; subst.
  apply H0.
  apply in_cons.
  assumption.
Qed.

Lemma LX4: forall d ic cs,
  is_supported_definition d ->
  get_trailing_cmds d ic = Some (cs) ->
  is_supported_cmd_list cs.
Proof.
Admitted.

Lemma step_supported : forall mdl s s',
  is_supported_module mdl ->
  module s = mdl ->
  step s s' ->
  is_supported_state s ->
  is_supported_state s'.
Proof.
  intros mdl s s' Hism Hm Hs His.
  inversion Hs; subst; inversion His; subst.
  {
    inversion H9; subst.
    apply IS_State.
    { apply (H0 c). apply in_eq. }
    { apply (LX3 c cs); assumption. }
  }
  { (* phi *)
    inversion H9; subst.
    apply IS_State.
    { apply (H0 c). apply in_eq. }
    { apply (LX3 c cs); assumption. }
  }
  { (* uncond branch *)
    inversion Hism; subst.
    apply LX1 in H.
    specialize (H3 d).
    apply H3 in H.
    apply LX2 in H0.
    inversion H; subst.
    apply H5 in H0.
    inversion H0; subst.
    rewrite H1 in H6.
    inversion H6; subst.
    apply IS_State.
    { apply H7. apply in_eq. }
    { apply (LX3 c cs); assumption. }
  }
  { (* true branch *)
    inversion Hism; subst.
    apply LX1 in H0.
    specialize (H4 d).
    apply H4 in H0.
    apply LX2 in H1.
    inversion H0; subst.
    apply H6 in H1.
    inversion H1; subst.
    rewrite H2 in H7.
    inversion H7; subst.
    apply IS_State.
    { apply H8. apply in_eq. }
    { apply (LX3 c cs); assumption. }
  }
  { (* false branch *)
    inversion Hism; subst.
    apply LX1 in H0.
    specialize (H4 d).
    apply H4 in H0.
    apply LX2 in H1.
    inversion H0; subst.
    apply H6 in H1.
    inversion H1; subst.
    rewrite H2 in H7.
    inversion H7; subst.
    apply IS_State.
    { apply H8. apply in_eq. }
    { apply (LX3 c cs); assumption. }
  }
  { (* Call *)
    inversion Hism; subst.
    apply LX0 in H.
    specialize (H5 d).
    apply H5 in H.
    apply LX2 in H1.
    inversion H; subst.
    apply H7 in H1.
    inversion H1; subst.
    rewrite H2 in H8.
    inversion H8; subst.
    apply IS_State.
    { apply H9. apply in_eq. }
    { apply (LX3 c' cs'); assumption. }
  }
  { (* VoidCall *)
    inversion Hism; subst.
    apply LX0 in H.
    specialize (H5 d).
    apply H5 in H.
    apply LX2 in H1.
    inversion H; subst.
    apply H7 in H1.
    inversion H1; subst.
    rewrite H2 in H8.
    inversion H8; subst.
    apply IS_State.
    { apply H9. apply in_eq. }
    { apply (LX3 c' cs'); assumption. }
  }
  { (* RetVoid *)
    inversion Hism; subst.
    apply LX1 in H.
    specialize (H2 d).
    apply H2 in H.
    apply LX4 in H0; try assumption.
    inversion H0; subst.
    apply IS_State.
    { apply H4. apply in_eq. }
    { apply (LX3 c' cs'); assumption. }
  }
  { (* Ret *)
    inversion Hism; subst.
    apply LX1 in H0.
    specialize (H3 d).
    apply H3 in H0.
    apply LX4 in H1; try assumption.
    inversion H1; subst.
    apply IS_State.
    { apply H5. apply in_eq. }
    { apply (LX3 c' cs'); assumption. }
  }
  { (* make_symbolic: similar to op *)
    inversion H11; subst.
    apply IS_State.
    { apply (H2 c). apply in_eq. }
    { apply (LX3 c cs); assumption. }
  }
  { (* assume: *)
    inversion H13; subst.
    apply IS_State.
    { apply (H4 c). apply in_eq. }
    { apply (LX3 c cs); assumption. }
  }
Qed.

Lemma step_same_module : forall mdl s s',
  module s = mdl ->
  step s s' ->
  module s' = mdl.
Proof.
Admitted.

Lemma multi_step_supported : forall mdl s s',
  is_supported_module mdl ->
  module s = mdl ->
  multi_step s s' ->
  is_supported_state s ->
  (module s' = mdl /\ is_supported_state s').
Proof.
  intros mdl s s' Hism Hm Hms His.
  induction Hms as [s s' | s s' s''].
  {
    split.
    { apply step_same_module with (s := s); assumption. }
    { apply (step_supported mdl s s'); assumption. }
  }
  {
    apply IHHms in His.
    {
      destruct His as [His_1 His_2].
      split.
      { apply step_same_module with (s := s'); assumption. }
      { apply (step_supported mdl s' s''); assumption. }
    }
    { inversion Hm; subst. reflexivity. }
  }
Qed.
