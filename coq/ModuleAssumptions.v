From Coq Require Import List.
From Coq Require Import PArith.BinPos.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import LLVMAst.
From SE Require Import LLVMUtils.
From SE Require Import Symbolic.

(* TODO: uncomment stuff *)

Inductive is_supported_ibinop : ibinop -> Prop :=
  | IS_Add : is_supported_ibinop (Add false false)
(*
  | IS_Sub : is_supported_ibinop (Sub false false)
  | IS_Mul : is_supported_ibinop (Mul false false)
  | IS_URem : is_supported_ibinop URem
  | IS_SRem : is_supported_ibinop SRem
  | IS_And : is_supported_ibinop And
  | IS_Or : is_supported_ibinop Or
  | IS_Xor : is_supported_ibinop Xor
*)
.

Inductive is_supported_div : ibinop -> Prop :=
  | IS_UDiv : is_supported_div (UDiv false)
(*
  | IS_SDiv : is_supported_div (SDiv false)
*)
.

Inductive is_supported_shift : ibinop -> Prop :=
  | IS_Shl : is_supported_shift (Shl false false)
(*
  | IS_LShr : is_supported_shift (LShr false)
  | IS_AShr : is_supported_shift (AShr false)
*)
.

Inductive is_supported_conv : conversion_type -> Prop :=
  | IS_ZExt : is_supported_conv Zext
  | IS_SExt : is_supported_conv Sext
  | IS_Trunc : is_supported_conv Trunc
  | IS_Bitcast : is_supported_conv Bitcast
.

(* TODO: rename to is_safe_exp/is_simple_expr? *)
Inductive is_supported_exp : llvm_exp -> Prop :=
  | IS_EXP_Ident : forall id,
      is_supported_exp (EXP_Ident id)
  | IS_EXP_Integer : forall x,
      is_supported_exp (EXP_Integer x)
  | IS_OP_IBinop : forall op t e1 e2,
      is_supported_exp e1 ->
      is_supported_exp e2 ->
      is_supported_ibinop op ->
      is_supported_exp (OP_IBinop op t e1 e2)
  | IS_OP_ICmp : forall op t e1 e2,
      is_supported_exp e1 ->
      is_supported_exp e2 ->
      is_supported_exp (OP_ICmp op t e1 e2)
  | IS_OP_Conversion : forall conv t1 e t2,
      is_supported_conv conv ->
      is_supported_exp e ->
      is_supported_exp (OP_Conversion conv t1 e t2)
.

Inductive is_supported_function_arg : function_arg -> Prop :=
  | IS_FunctionArg : forall t e attrs,
      is_supported_exp e ->
      is_supported_function_arg ((t, e), attrs)
.

Inductive is_supported_cmd : llvm_cmd -> Prop :=
  | IS_INSTR_Op : forall n v e,
      is_supported_exp e ->
      is_supported_cmd (CMD_Inst n (INSTR_Op v e))
  | IS_INSTR_Op_UDiv : forall n v t e1 e2,
      is_supported_exp e1 ->
      is_supported_exp e2 ->
      is_supported_cmd (CMD_Inst n (INSTR_Op v (OP_IBinop (UDiv false) t e1 e2)))
  | IS_Phi : forall n v t args,
      (forall bid e, In (bid, e) args -> is_supported_exp e) ->
      is_supported_cmd (CMD_Phi n (Phi v t args))
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
  | IS_Term_Unreachable : forall n,
      is_supported_cmd (CMD_Term n TERM_Unreachable)
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
  | IS_Global : forall (g : llvm_global) (e : llvm_exp),
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
      is_supported_module mdl ->
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

Lemma is_supported_propagation : forall mdl fid d bid b cs,
  is_supported_module mdl ->
  find_function mdl fid = Some d ->
  fetch_block d bid = Some b ->
  (blk_cmds b) = cs ->
  is_supported_cmd_list cs.
Proof.
  intros mdl fid d bid b cs Hism Hf Hb Hcs.
  inversion Hism; subst.
  apply LX1 in Hf.
  apply H0 in Hf.
  inversion Hf; subst.
  apply LX2 in Hb.
  apply H1 in Hb.
  inversion Hb; subst.
  assumption.
Qed.

Lemma is_supported_propagation_with_exp : forall mdl e d b cs,
  is_supported_module mdl ->
  find_function_by_exp mdl e = Some d ->
  entry_block d = Some b ->
  (blk_cmds b) = cs ->
  is_supported_cmd_list cs.
Proof.
  intros mdl e d b cs Hism Hf Hb Hcs.
  unfold find_function_by_exp in Hf.
  destruct e eqn:Ee; try inversion Hf.
  destruct id as [fid | fid] eqn:Eid; try inversion Hf.
  unfold entry_block in Hb.
  apply (is_supported_propagation mdl fid d (init (df_body d)) b cs); assumption.
Qed.

Lemma trailing_cmds_subset : forall cs ic cs',
  get_trailing_cmds_by_cid cs ic = Some cs' ->
  (forall c, In c cs' -> In c cs).
Proof.
  intros cs ic cs' Heq.
  generalize dependent cs'.
  induction cs as [ | c tail]. intros cs' Heq.
  {
    simpl in Heq.
    inversion Heq.
  }
  {
    intros cs' Ht.
    intros c' Hin.
    simpl in Ht.
    destruct (PeanoNat.Nat.eqb (get_cmd_id c) ic) eqn:E.
    {
      inversion Ht; subst.
      assumption.
    }
    {
      apply IHtail with (c := c') in Ht; try assumption.
      apply in_cons.
      assumption.
    }
  }
Qed.

Lemma is_supported_propagation_traling_cmds : forall mdl fid d ic cs,
  is_supported_module mdl ->
  find_function mdl fid = Some d ->
  get_trailing_cmds d ic = Some cs ->
  is_supported_cmd_list cs.
Proof.
  intros mdl fid d ic cs Hism Hf Ht.
  unfold get_trailing_cmds in Ht.
  destruct (fetch_block d (ic_bid ic)) as [b | ] eqn:E.
  {
    apply IS_CmdList.
    assert(L : forall c, In c cs -> In c (blk_cmds b)).
    { apply trailing_cmds_subset with (ic := (ic_cid ic)). assumption. }
    destruct (blk_cmds b) as [ | c' cs'] eqn:Ecmds.
    { simpl in Ht. inversion Ht. }
    {
      apply (is_supported_propagation mdl fid d (ic_bid ic) b (c' :: cs')) in Hism;
      try assumption.
      inversion Hism; subst.
      intros c Hin.
      apply H.
      apply L.
      assumption.
    }
  }
  { inversion Ht. }
Qed.

Lemma is_supported_state_lemma : forall ic c cs pbid ls stk gs mdl,
  is_supported_module mdl ->
  is_supported_cmd_list (c :: cs) ->
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
    ).
Proof.
  intros ic c cs pbid ls stk gs mdl Hism H.
  inversion H; subst.
  apply IS_State.
  { apply H0. apply in_eq. }
  {
    apply IS_CmdList.
    intros c' Hin.
    apply H0.
    apply in_cons.
    assumption.
  }
  { assumption. }
Qed.

Lemma is_supported_init_state : forall mdl fid s,
  is_supported_module mdl ->
  init_state mdl fid = Some s -> is_supported_state s.
Proof.
  intros mdl fid s Hism Heq.
  unfold init_state in Heq.
  destruct (find_function mdl fid) as [d | ] eqn:Ed; try discriminate Heq.
  destruct (build_inst_counter mdl d) as [ic | ] eqn:Eic; try discriminate Heq.
  destruct (entry_block d) as [b | ] eqn:Eb; try discriminate Heq.
  destruct (blk_cmds b) as [ | c cs ] eqn:Ecs; try discriminate Heq.
  inversion Heq; subst.
  apply is_supported_state_lemma; try assumption.
  unfold entry_block in Eb.
  apply (is_supported_propagation mdl fid d (init (df_body d)) b (c :: cs)); assumption.
Qed.

Lemma is_supported_step : forall s s',
  step s s' ->
  is_supported_state s ->
  is_supported_state s'.
Proof.
  intros s s' Hs His.
  inversion Hs; subst; inversion His; subst.
  { apply is_supported_state_lemma; assumption. }
  { apply is_supported_state_lemma; assumption. }
  {
    apply is_supported_state_lemma; try assumption.
    apply (is_supported_propagation mdl (ic_fid ic) d tbid b (c :: cs)); assumption.
  }
  {
    apply is_supported_state_lemma; try assumption.
    apply (is_supported_propagation mdl (ic_fid ic) d bid1 b (c :: cs)); assumption.
  }
  {
    apply is_supported_state_lemma; try assumption.
    apply (is_supported_propagation mdl (ic_fid ic) d bid2 b (c :: cs)); assumption.
  }
  {
    apply is_supported_state_lemma; try assumption.
    apply (is_supported_propagation_with_exp mdl f d b (c' :: cs')); assumption.
  }
  {
    apply is_supported_state_lemma; try assumption.
    apply (is_supported_propagation_with_exp mdl f d b (c' :: cs')); assumption.
  }
  {
    apply is_supported_state_lemma; try assumption.
    apply (is_supported_propagation_traling_cmds mdl (ic_fid ic') d ic' (c' :: cs')); assumption.
  }
  {
    apply is_supported_state_lemma; try assumption.
    apply (is_supported_propagation_traling_cmds mdl (ic_fid ic') d ic' (c' :: cs')); assumption.
  }
  { apply is_supported_state_lemma; assumption. }
  { apply is_supported_state_lemma; assumption. }
Qed.

Lemma is_supported_multi_step : forall s s',
  multi_step s s' ->
  is_supported_state s ->
  is_supported_state s'.
Proof.
  intros s s' Hms His.
  induction Hms as [s s' | s s' s''].
  {
    { apply (is_supported_step s s'); assumption. }
  }
  {
    apply IHHms in His.
    apply (is_supported_step s' s''); assumption.
  }
Qed.

Inductive is_supported_sym_state : sym_state -> Prop :=
  | IS_SymState : forall ic c cs pbid ls stk gs syms pc mdl,
      is_supported_cmd c ->
      is_supported_cmd_list cs ->
      is_supported_module mdl ->
      is_supported_sym_state
        (mk_sym_state
          ic
          c
          cs
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
.

Lemma is_supported_sym_state_lemma : forall ic c cs pbid ls stk gs syms pc mdl,
  is_supported_module mdl ->
  is_supported_cmd_list (c :: cs) ->
  is_supported_sym_state
    (mk_sym_state
      ic
      c
      cs
      pbid
      ls
      stk
      gs
      syms
      pc
      mdl
    ).
Proof.
  intros ic c cs pbid ls stk gs syms pc mdl Hism H.
  inversion H; subst.
  apply IS_SymState.
  { apply H0. apply in_eq. }
  {
    apply IS_CmdList.
    intros c' Hin.
    apply H0.
    apply in_cons.
    assumption.
  }
  { assumption. }
Qed.

Lemma is_supported_init_sym_state : forall mdl fid s,
  is_supported_module mdl ->
  init_sym_state mdl fid = Some s -> is_supported_sym_state s.
Proof.
  intros mdl fid s Hism Heq.
  unfold init_sym_state in Heq.
  destruct (find_function mdl fid) as [d | ] eqn:Ed; try discriminate Heq.
  destruct (build_inst_counter mdl d) as [ic | ] eqn:Eic; try discriminate Heq.
  destruct (entry_block d) as [b | ] eqn:Eb; try discriminate Heq.
  destruct (blk_cmds b) as [ | c cs ] eqn:Ecs; try discriminate Heq.
  inversion Heq; subst.
  apply is_supported_sym_state_lemma; try assumption.
  unfold entry_block in Eb.
  apply (is_supported_propagation mdl fid d (init (df_body d)) b (c :: cs)); assumption.
Qed.

Lemma is_supported_sym_step : forall s s',
  sym_step s s' ->
  is_supported_sym_state s ->
  is_supported_sym_state s'.
Proof.
  intros s s' Hs His.
  inversion Hs; subst; inversion His; subst.
  { apply is_supported_sym_state_lemma; assumption. }
  { apply is_supported_sym_state_lemma; assumption. }
  {
    apply is_supported_sym_state_lemma; try assumption.
    apply (is_supported_propagation mdl (ic_fid ic) d tbid b (c :: cs)); assumption.
  }
  {
    apply is_supported_sym_state_lemma; try assumption.
    apply (is_supported_propagation mdl (ic_fid ic) d bid1 b (c :: cs)); assumption.
  }
  {
    apply is_supported_sym_state_lemma; try assumption.
    apply (is_supported_propagation mdl (ic_fid ic) d bid2 b (c :: cs)); assumption.
  }
  {
    apply is_supported_sym_state_lemma; try assumption.
    apply (is_supported_propagation_with_exp mdl f d b (c' :: cs')); assumption.
  }
  {
    apply is_supported_sym_state_lemma; try assumption.
    apply (is_supported_propagation_with_exp mdl f d b (c' :: cs')); assumption.
  }
  {
    apply is_supported_sym_state_lemma; try assumption.
    apply (is_supported_propagation_traling_cmds mdl (ic_fid ic') d ic' (c' :: cs')); assumption.
  }
  {
    apply is_supported_sym_state_lemma; try assumption.
    apply (is_supported_propagation_traling_cmds mdl (ic_fid ic') d ic' (c' :: cs')); assumption.
  }
  { apply is_supported_sym_state_lemma; assumption. }
  { apply is_supported_sym_state_lemma; assumption. }
Qed.

Lemma sym_step_preserves_module : forall mdl s s',
  sym_module s = mdl ->
  sym_step s s' ->
  sym_module s' = mdl.
Proof.
  intros mdl s s' Heq Hs.
  inversion Hs; subst; reflexivity.
Qed.

Lemma is_supported_multi_sym_step : forall s s',
  multi_sym_step s s' ->
  is_supported_sym_state s ->
  is_supported_sym_state s'.
Proof.
  intros s s' Hms His.
  induction Hms as [s s' | s s' s''].
  {
    { apply (is_supported_sym_step s s'); assumption. }
  }
  {
    apply IHHms in His.
    apply (is_supported_sym_step s' s''); assumption.
  }
Qed.
