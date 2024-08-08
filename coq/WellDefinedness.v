From Coq Require Import List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import Symbolic.
From SE Require Import Relation.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

From SE.Utils Require Import ListUtil.
From SE.Utils Require Import Util.

(* TODO: ... *)
Inductive well_defined_smt_expr : smt_expr -> list string -> Prop :=
.

Inductive well_defined_smt_store : smt_store -> list string -> Prop :=
  | WD_SMTStore : forall s syms,
      (forall x n se, (s x) = Some se -> subexpr (SMT_Var n) se -> In n syms) ->
      well_defined_smt_store s syms
.

Inductive well_defined_stack : list sym_frame -> list string -> Prop :=
  | WD_EmptyStack : forall syms,
      well_defined_stack [] syms
  | WD_Frame : forall ls ic pbid v stk syms,
      well_defined_smt_store ls syms ->
      well_defined_stack stk syms ->
      well_defined_stack ((Sym_Frame ls ic pbid v) :: stk) syms
  | WD_FrameNoReturn : forall ls ic pbid stk syms,
      well_defined_smt_store ls syms ->
      well_defined_stack stk syms ->
      well_defined_stack ((Sym_Frame_NoReturn ls ic pbid) :: stk) syms
.

Inductive well_defined : sym_state -> Prop :=
  | WD_State : forall ic c cs pbid ls stk gs syms pc mdl,
      (
        well_defined_smt_store ls syms /\
        well_defined_smt_store gs syms /\
        well_defined_stack stk syms /\
        (forall n, subexpr (SMT_Var n) pc -> In n syms)
      ) ->
      well_defined
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

Lemma well_defined_init_sym_state :
  forall mdl d, exists s, (init_sym_state mdl d) = Some s -> well_defined s.
Proof.
Admitted.

(* TODO: remove? *)
Lemma subexpr_ibinop : forall e op e1 e2,
  e <> (sym_eval_ibinop op e1 e2) ->
  subexpr e (sym_eval_ibinop op e1 e2) ->
  subexpr e e1 \/ subexpr e e2 .
Proof.
  intros e op e1 e2 Hneq Hse.
  destruct op; simpl in Hse; (
    inversion Hse; subst;
    [
      destruct Hneq; reflexivity |
      left; assumption |
      right; assumption
    ]
  ).
Qed.

Lemma subexpr_var_ibinop : forall x op e1 e2,
  subexpr (SMT_Var x) (sym_eval_ibinop op e1 e2) ->
  subexpr (SMT_Var x) e1 \/ subexpr (SMT_Var x) e2 .
Proof.
  intros x op e1 e2 Hse.
  destruct op; simpl in Hse; (
    inversion Hse; subst;
    [
      left; assumption |
      right; assumption
    ]
  ).
Qed.

Lemma subexpr_var_icmp : forall x op e1 e2,
  subexpr (SMT_Var x) (sym_eval_icmp op e1 e2) ->
  subexpr (SMT_Var x) e1 \/ subexpr (SMT_Var x) e2 .
Proof.
  intros x op e1 e2 Hse.
  destruct op; simpl in Hse; (
    inversion Hse; subst;
    [
      left; assumption |
      right; assumption
    ]
  ).
Qed.

Lemma subexpr_var_conv : forall x conv e1 t1 t2 e2,
  (sym_convert conv e1 t1 t2) = Some e2 ->
  subexpr (SMT_Var x) e2 ->
  subexpr (SMT_Var x) e1.
Proof.
  intros x conv e1 t1 t2 e2 Heq Hse.
  destruct conv; simpl in *.
  {
    destruct t1; try (discriminate Heq).
    {
      destruct t2; try (discriminate Heq).
      {
        destruct (w0 <=? w)%positive eqn:E.
        {
          injection Heq. clear Heq. intros Heq.
          subst.
          inversion Hse; subst.
          assumption.
        }
        { discriminate Heq. }
      }
    }
  }
  { admit. }
  { admit. }
  {
    injection Heq. clear Heq. intros Heq.
    subst.
    assumption.
  }
Admitted.

Lemma well_defined_sym_eval_exp : forall s ot e n se,
  (well_defined s) ->
  (sym_eval_exp (sym_store s) (sym_globals s) ot e) = Some se ->
  subexpr (SMT_Var n) se ->
  In n (sym_symbolics s).
Proof.
  intros s ot e n se Hwd Heq Hse.
  generalize dependent se.
  generalize dependent ot.
  induction e; intros ot se Heq Hse; inversion Hwd; subst; simpl in *.
  {
    unfold sym_lookup_ident.
    destruct H as [H_1 [H_2 H_3]].
    destruct id; simpl in Heq.
    {
      inversion H_2; subst.
      specialize (H id n se).
      apply H; assumption.
    }
    {
      inversion H_1; subst.
      specialize (H id n se).
      apply H; assumption.
    }
  }
  { admit. }
  {
    destruct b; simpl in Heq.
    {
      injection Heq. clear Heq.
      intros Heq.
      rewrite <- Heq in Hse.
      inversion Hse.
    }
    {
      injection Heq. clear Heq.  intros Heq.
      rewrite <- Heq in Hse.
      inversion Hse.
    }
  }
  {
    discriminate Heq.
  }
  {
    discriminate Heq.
  }
  {
    discriminate Heq.
  }
  {
    discriminate Heq.
  }
  {
    specialize (IHe1 (Some t)).
    specialize (IHe2 (Some t)).
    destruct (sym_eval_exp ls gs (Some t) e1) as [se1 | ] eqn:E1.
    {
      destruct (sym_eval_exp ls gs (Some t) e2) as [se2 | ] eqn:E2.
      {
        injection Heq. clear Heq. intros Heq.
        subst.
        apply subexpr_var_ibinop in Hse.
        destruct Hse as [Hse | Hse].
        {
          apply (IHe1 se1).
          { reflexivity. }
          { assumption. }
        }
        {
          apply (IHe2 se2).
          { reflexivity. }
          { assumption. }
        }
      }
      { discriminate Heq. }
    }
    { discriminate Heq. }
  }
  {
    specialize (IHe1 (Some t)).
    specialize (IHe2 (Some t)).
    destruct (sym_eval_exp ls gs (Some t) e1) as [se1 | ] eqn:E1.
    {
      destruct (sym_eval_exp ls gs (Some t) e2) as [se2 | ] eqn:E2.
      {
        injection Heq. clear Heq. intros Heq.
        subst.
        apply subexpr_var_icmp in Hse.
        destruct Hse as [Hse | Hse].
        {
          apply (IHe1 se1).
          { reflexivity. }
          { assumption. }
        }
        {
          apply (IHe2 se2).
          { reflexivity. }
          { assumption. }
        }
      }
      { discriminate Heq. }
    }
    { discriminate Heq. }
  }
  {
    specialize (IHe (Some t1)).
    destruct (sym_eval_exp ls gs (Some t1) e) as [se' | ] eqn:E.
    {
      apply (IHe se').
      { reflexivity. }
      {
        apply (subexpr_var_conv n conv se' t1 t2 se); assumption.
      }
    }
    { discriminate Heq. }
  }
  { discriminate Heq. }
Admitted.

Lemma well_defined_sym_eval_phi : forall s t args pbid n se,
  (well_defined s) ->
  (sym_eval_phi_args (sym_store s) (sym_globals s) t args pbid) = Some se ->
  subexpr (SMT_Var n) se ->
  In n (sym_symbolics s).
Proof.
  intros s t args pbid n se Hwd Heq Hse.
  induction args.
  {
    simpl in Heq.
    discriminate Heq.
  }
  {
    simpl in Heq.
    destruct a as [bid e].
    destruct (raw_id_eqb bid pbid) eqn:E in Heq.
    {
      apply (well_defined_sym_eval_exp
        s
        (Some t)
        e
        n
        se
      ); assumption.
    }
    {
      apply IHargs in Heq.
      assumption.
    }
  }
Qed.

Lemma well_defined_sym_eval_args : forall s args ses se n,
  (well_defined s) ->
  (sym_eval_args (sym_store s) (sym_globals s) args) = Some ses ->
  In se ses ->
  subexpr (SMT_Var n) se ->
  In n (sym_symbolics s).
Proof.
  intros s args ses se n Hwd Heq Hin Hse.
  generalize dependent se.
  generalize dependent ses.
  induction args; intros ses Heq se Hin Hse.
  {
    simpl in Heq.
    inversion Heq; subst.
    inversion Hin.
  }
  {
    simpl in Heq.
    destruct (sym_eval_arg (sym_store s) (sym_globals s) a) eqn:Earg.
    {
      destruct (sym_eval_args (sym_store s) (sym_globals s) args) eqn:Eargs.
      {
        inversion Heq; subst.
        inversion Hin; subst.
        {
          unfold sym_eval_arg in Earg.
          destruct a, t.
          apply (well_defined_sym_eval_exp _ (Some t) e n se); assumption.
        }
        {
          apply IHargs with (ses := l) (se := se).
          { reflexivity. }
          { assumption. }
          { assumption. }
        }
      }
      { discriminate Heq. }
    }
    { discriminate Heq. }
  }
Qed.

Lemma L0 : forall d se ses ls,
  create_local_smt_store d (se :: ses) = Some ls ->
  exists x ls',
    (create_local_smt_store d ses) = Some ls' /\
    (x !-> Some se; ls') = ls.
Proof.
Admitted.

(* TODO: rename *)
Lemma L1 : forall ses syms d ls,
  (forall se n, In se ses -> subexpr (SMT_Var n) se -> In n syms) ->
  (create_local_smt_store d ses) = Some ls ->
  well_defined_smt_store ls syms.
Proof.
  intros ses syms d ls Hwd H.
  generalize dependent ls.
  induction ses; intros ls H.
  {
    unfold create_local_smt_store in H.
    destruct (df_args d) eqn:Eargs; simpl in H.
    {
      inversion H; subst.
      apply WD_SMTStore.
      intros x n se Heq Hse.
      inversion Heq.
    }
    { discriminate H. }
  }
  {
    apply L0 in H.
    destruct H as [y [ls' [H1 H2]]].
    assert(Hls': well_defined_smt_store ls' syms).
    {
      apply IHses.
      {
        intros se n Hin Hse.
        apply (Hwd se n).
        { apply in_cons; assumption. }
        { assumption. }
      }
      { assumption. }
    }
    subst.
    apply WD_SMTStore.
    intros x n se Heq Hse.
    destruct (x =? y) eqn:E.
    {
      rewrite raw_id_eqb_eq in E.
      subst.
      rewrite update_map_eq in Heq.
      inversion Heq; subst.
      apply (Hwd se n).
      { apply in_eq. }
      { assumption. }
    }
    {
      rewrite raw_id_eqb_neq in E.
      rewrite update_map_neq in Heq.
      {
        inversion Hls'; subst.
        apply (H x n se); assumption.
      }
      { symmetry. assumption. }
    }
  }
Qed.

Lemma well_defined_smt_store_ext : forall s sym syms,
  well_defined_smt_store s syms -> well_defined_smt_store s (sym :: syms).
Proof.
  intros s sym syms Hwd.
  inversion Hwd; subst.
  apply WD_SMTStore.
  intros x n se Heq Hse.
  apply in_cons.
  apply (H x n se); assumption.
Qed.

Lemma well_defined_stack_ext : forall stk sym syms,
  well_defined_stack stk syms -> well_defined_stack stk (sym :: syms).
Proof.
  intros stk sym syms Hwd.
  induction Hwd.
  { apply WD_EmptyStack. }
  {
    apply WD_Frame.
    {
      apply well_defined_smt_store_ext.
      assumption.
    }
    { assumption. }
  }
  {
    apply WD_FrameNoReturn.
    {
      apply well_defined_smt_store_ext.
      assumption.
    }
    { assumption. }
  }
Qed.

Lemma well_defined_sym_step : forall (s s' : sym_state),
  well_defined s -> sym_step s s' -> well_defined s'
.
Proof.
  intros s s' Hwd Hstep.
  destruct s as [ic c cs pbid ls stk gs syms pc mdl].
  inversion Hwd; subst.
  destruct H0 as [Hwd_ls [Hwd_gs [Hwd_stk Hwd_pc]]].
  (* TODO: this inversion renames state variables *)
  inversion Hstep; subst.
  {
    apply WD_State.
    split.
    {
      inversion Hwd_ls; subst.
      apply WD_SMTStore.
      intros x n se' Heq Hse.
      destruct (raw_id_eqb x v) eqn:E.
      {
        rewrite raw_id_eqb_eq in E.
        rewrite E in *. clear E.
        rewrite update_map_eq in Heq.
        injection Heq. clear Heq. intros Heq.
        rewrite <- Heq in *. clear Heq.
        apply (well_defined_sym_eval_exp
          (mk_sym_state
            ic
            (CMD_Inst cid (INSTR_Op v e))
            (c0 :: cs0)
            pbid
            ls
            stk
            gs
            syms
            pc
            mdl
          )
          None
          e
          n
          se
        ); assumption.
      }
      {
        rewrite raw_id_eqb_neq in E.
        rewrite update_map_neq in Heq.
        apply (H x n se'); assumption.
        symmetry.
        assumption.
      }
    }
    {
      split.
      { assumption. }
      { split; assumption. }
    }
  }
  {
    apply WD_State.
    split.
    {
      apply WD_SMTStore.
      intros x n se' Heq Hse.
      destruct (raw_id_eqb x v) eqn:E.
      {
        rewrite raw_id_eqb_eq in E.
        rewrite E in *. clear E.
        rewrite update_map_eq in Heq.
        injection Heq. clear Heq. intros Heq.
        rewrite <- Heq in *. clear Heq.
        apply (well_defined_sym_eval_phi
          (mk_sym_state
            ic
            (CMD_Phi cid (Phi v t args))
            (c0 :: cs0)
            (Some pbid0)
            ls
            stk
            gs
            syms
            pc
            mdl
          )
          t
          args
          pbid0
          n
          se
        ); assumption.
      }
      {
        inversion Hwd_ls; subst.
        rewrite raw_id_eqb_neq in E.
        rewrite update_map_neq in Heq.
        apply (H x n se'); assumption.
        symmetry.
        assumption.
      }
    }
    {
      split.
      { assumption. }
      { split; assumption. }
    }
  }
  {
    apply WD_State.
    split.
    { assumption. }
    {
      split.
      { assumption. }
      { split; assumption. }
    }
  }
  {
    apply WD_State.
    split.
    { assumption. }
    {
      split.
      { assumption. }
      {
        split.
        { assumption. }
        intros n Hse.
        inversion Hse; subst.
        {
          apply Hwd_pc.
          assumption.
        }
        {
          apply (well_defined_sym_eval_exp
            (mk_sym_state
              ic
              (CMD_Term cid (TERM_Br (t, e) bid1 bid2))
              []
              pbid
              ls
              stk
              gs
              syms
              pc
              mdl
            )
            (Some t)
            e
            n
            se
          ); assumption.
        }
      }
    }
  }
  {
    apply WD_State.
    split.
    { assumption. }
    {
      split.
      { assumption. }
      {
        split.
        { assumption. }
        {
          intros n Hse.
          inversion Hse; subst.
          {
            apply Hwd_pc.
            assumption.
          }
          {
            inversion H1; subst.
            apply (well_defined_sym_eval_exp
              (mk_sym_state
                ic
                (CMD_Term cid (TERM_Br (t, e) bid1 bid2))
                []
                pbid
                ls
                stk
                gs
                syms
                pc
                mdl
              )
              (Some t)
              e
              n
              se
            ); assumption.
          }
        }
      }
    }
  }
  {
    apply WD_State.
    split.
    {
      apply (L1 ses syms d ls').
      {
        intros se n Hin Hse.
        apply (well_defined_sym_eval_args
          (mk_sym_state
            ic
            (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, f) args anns))
            (c0 :: cs0)
            pbid
            ls
            stk
            gs
            syms
            pc
            mdl
          )
          args
          ses
          se
          n
        ); assumption.
      }
      { assumption. }
    }
    {
      split.
      { assumption. }
      {
        split.
        { apply WD_FrameNoReturn; assumption. }
        { assumption. }
      }
    }
  }
  { admit. }
  {
    apply WD_State.
    inversion Hwd_stk; subst.
    split.
    { assumption.  }
    {
      split.
      { assumption. }
      { split; assumption. }
    }
  }
  { admit. }
  {
    apply WD_State.
    split.
    { assumption. }
    {
      split.
      { assumption. }
      {
        split.
        { assumption. }
        intros n Hse.
        inversion Hse; subst.
        {
          apply Hwd_pc.
          assumption.
        }
        {
          apply (well_defined_sym_eval_exp
            (mk_sym_state
              ic
              (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, klee_assume_exp) [(t, e, attrs)] []))
              (c0 :: cs0)
              pbid
              ls
              stk
              gs
              syms
              pc
              mdl
            )
            (Some t)
            e
            n
            se
          ).
          { assumption. }
          { assumption. }
          {
            apply (subexpr_var_conv n Trunc se t (TYPE_I 1) cond); assumption.
          }
        }
      }
    }
  }
  {
    apply WD_State.
    split.
    {
      inversion Hwd_ls; subst.
      apply WD_SMTStore.
      intros x n se' Heq Hse.
      destruct (raw_id_eqb x v) eqn:E.
      {
        rewrite raw_id_eqb_eq in E.
        rewrite E in *. clear E.
        rewrite update_map_eq in Heq.
        injection Heq. clear Heq. intros Heq.
        subst.
        inversion Hse; subst.
        apply in_eq.
      }
      {
        rewrite raw_id_eqb_neq in E.
        rewrite update_map_neq in Heq.
        apply in_cons.
        apply (H x n se'); try assumption.
        symmetry.
        assumption.
      }
    }
    {
      split.
      {
        apply well_defined_smt_store_ext.
        assumption.
      }
      {
        split.
        {
          apply well_defined_stack_ext.
          assumption.
        }
        {
          intros n Hse.
          apply in_cons.
          apply Hwd_pc.
          assumption.
        }
      }
    }
  }
Admitted.

Lemma well_defined_multi_sym_step : forall s s',
  (well_defined s) -> (multi_sym_step s s') -> (well_defined s').
Proof.
Admitted.
