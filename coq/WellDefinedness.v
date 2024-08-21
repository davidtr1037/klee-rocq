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

(*
  | WD_Expr : forall se syms,
      (forall n, subexpr (SMT_Var n) se -> In n syms) ->
      well_defined_smt_expr se syms
*)

Inductive well_defined_smt_expr : smt_expr -> list string -> Prop :=
  | WD_Expr : forall se syms,
      (forall n, contains_var se n -> In n syms) ->
      well_defined_smt_expr se syms
.

Inductive well_defined_smt_store : smt_store -> list string -> Prop :=
  | WD_SMTStore : forall s syms,
      (forall x se, (s x) = Some se -> well_defined_smt_expr se syms) ->
      well_defined_smt_store s syms
.

Inductive well_defined_stack : list sym_frame -> list string -> Prop :=
  | WD_EmptyStack : forall syms,
      well_defined_stack [] syms
  | WD_Frame : forall ls ic pbid v stk syms,
      well_defined_smt_store ls syms ->
      well_defined_stack stk syms ->
      well_defined_stack ((Sym_Frame ls ic pbid v) :: stk) syms
.

(* TODO: use record getters? *)
(* TODO: avoid conjunction *)
Inductive well_defined : sym_state -> Prop :=
  | WD_State : forall ic c cs pbid ls stk gs syms pc mdl,
      (
        well_defined_smt_store ls syms /\
        well_defined_smt_store gs syms /\
        well_defined_stack stk syms /\
        well_defined_smt_expr pc syms
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

(* TODO: rename *)
Lemma subexpr_var_not : forall x e,
  contains_var (SMT_Not e) x -> contains_var e x.
Proof.
Admitted.

(* TODO: rename *)
Lemma subexpr_var_binop : forall x op e1 e2,
  contains_var (SMT_BinOp op e1 e2) x ->
  contains_var e1 x \/ contains_var e2 x.
Proof.
Admitted.

(* TODO: rename *)
Lemma subexpr_var_ibinop : forall x op e1 e2,
  contains_var (sym_eval_ibinop op e1 e2) x ->
  contains_var e1 x \/ contains_var e2 x.
Proof.
Admitted.
(*
  intros x op e1 e2 Hse.
  destruct op; simpl in Hse; (
    inversion Hse; subst;
    [
      left; assumption |
      right; assumption
    ]
  ).
Qed.
*)

(* TODO: rename *)
Lemma subexpr_var_icmp : forall x op e1 e2,
  contains_var (sym_eval_icmp op e1 e2) x ->
  contains_var e1 x \/ contains_var e2 x.
Proof.
Admitted.
(*
  intros x op e1 e2 Hse.
  destruct op; simpl in Hse; (
    inversion Hse; subst;
    [
      left; assumption |
      right; assumption
    ]
  ).
Qed.
*)

(* TODO: rename *)
Lemma subexpr_var_conv : forall x conv e1 t1 t2 e2,
  (sym_convert conv e1 t1 t2) = Some e2 ->
  contains_var e2 x ->
  contains_var e1 x.
Proof.
Admitted.
(*
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
  {
    destruct t1; try (discriminate Heq).
    {
      destruct t2; try (discriminate Heq).
      {
        destruct (w0 =? w)%positive eqn:E1.
        {
          inversion Heq; subst.
          assumption.
        }
        {
          destruct (w0 <=? w)%positive eqn:E2.
          {
            inversion Heq; subst.
            inversion Hse; subst.
            assumption.
          }
          {
            inversion Heq; subst.
            inversion Hse; subst.
            assumption.
          }
        }
      }
    }
  }
  {
    destruct t1; try (discriminate Heq).
    {
      destruct t2; try (discriminate Heq).
      {
        destruct (w0 =? w)%positive eqn:E1.
        {
          inversion Heq; subst.
          assumption.
        }
        {
          destruct (w0 <=? w)%positive eqn:E2.
          {
            inversion Heq; subst.
            inversion Hse; subst.
            assumption.
          }
          {
            inversion Heq; subst.
            inversion Hse; subst.
            assumption.
          }
        }
      }
    }
  }
  {
    injection Heq. clear Heq. intros Heq.
    subst.
    assumption.
  }
Qed.
*)

(* TODO: rename *)
Lemma well_defined_smt_expr_ext : forall se sym syms,
  well_defined_smt_expr se syms ->
  well_defined_smt_expr se (sym :: syms).
Proof.
  intros se sym syms Hwd.
  apply WD_Expr.
  intros n Hse.
  apply in_cons.
  inversion Hwd; subst.
  apply H.
  assumption.
Qed.

Lemma well_defined_empty_smt_store : forall syms, well_defined_smt_store empty_smt_store syms.
Proof.
  intros syms.
  apply WD_SMTStore.
  intros x se Heq.
  inversion Heq; subst.
Qed.

Lemma well_defined_init_sym_state : forall mdl fid s,
  (init_sym_state mdl fid) = Some s -> well_defined s.
Proof.
  intros mdl fid s H.
  unfold init_sym_state in H.
  destruct (find_function mdl fid) as [s_d | ] eqn:Es_d; try discriminate H.
  destruct (build_inst_counter mdl s_d) as [s_ic | ] eqn:Es_ic; try discriminate H.
  destruct (entry_block s_d) as [s_b | ] eqn:Es_b; try discriminate H.
  destruct (blk_cmds s_b) as [ | s_cmd s_cmds ] eqn:Es_cs; try discriminate H.
  inversion H; subst.
  apply WD_State.
  split.
  {
    unfold init_local_smt_store.
    apply well_defined_empty_smt_store.
  }
  {
    split.
    {
      unfold init_local_smt_store.
      apply well_defined_empty_smt_store.
    }
    {
      split.
      { apply WD_EmptyStack. }
      {
        apply WD_Expr.
        intros n Hse.
        inversion Hse; subst; inversion H0.
      }
    }
  }
Qed.

Lemma well_defined_smt_store_update : forall ls x se syms,
  well_defined_smt_store ls syms ->
  well_defined_smt_expr se syms ->
  well_defined_smt_store (x !-> Some se; ls) syms.
Proof.
  intros ls x se syms Hwd1 Hwd2.
  apply WD_SMTStore.
  intros x' se' Heq.
  destruct (raw_id_eqb x x') eqn:E.
  {
    rewrite raw_id_eqb_eq in E.
    subst.
    rewrite update_map_eq in Heq.
    inversion Heq; subst.
    assumption.
  }
  {
    rewrite raw_id_eqb_neq in E.
    rewrite update_map_neq in Heq.
    {
      inversion Hwd1; subst.
      apply (H x' se'); assumption.
    }
    { assumption. }
  }
Qed.

(* TODO: rename *)
Lemma well_defined_smt_store_ext : forall s sym syms,
  well_defined_smt_store s syms -> well_defined_smt_store s (sym :: syms).
Proof.
  intros s sym syms Hwd.
  inversion Hwd; subst.
  apply WD_SMTStore.
  intros x se Heq.
  apply well_defined_smt_expr_ext.
  apply (H x se).
  assumption.
Qed.

Lemma well_defined_sym_eval_exp : forall ls gs ot e se syms,
  well_defined_smt_store ls syms ->
  well_defined_smt_store gs syms ->
  (sym_eval_exp ls gs ot e) = Some se ->
  well_defined_smt_expr se syms.
Proof.
  intros ls gs ot e se syms Hwd_ls Hwd_gs Heq.
  generalize dependent se.
  generalize dependent ot.
  induction e; intros ot se Heq; simpl in *.
  {
    unfold sym_lookup_ident.
    destruct id as [x | x] eqn:E; simpl in Heq.
    {
      inversion Hwd_gs; subst.
      specialize (H x se).
      apply H; assumption.
    }
    {
      inversion Hwd_ls; subst.
      specialize (H x se).
      apply H; assumption.
    }
  }
  {
    destruct ot eqn:Eot.
    {
      destruct t eqn:Et; inversion Heq.
      repeat (destruct w; simpl in Heq; try (inversion Heq));
      (
        inversion Heq; subst;
        apply WD_Expr;
        intros n Hse;
        inversion Hse; subst; inversion H
      ).
    }
    { inversion Heq. }
  }
  {
    destruct b; simpl in Heq.
    {
      injection Heq. clear Heq.  intros Heq.
      rewrite <- Heq.
      apply WD_Expr.
      intros n Hse.
      inversion Hse; subst; inversion H.
    }
    {
      injection Heq. clear Heq.  intros Heq.
      rewrite <- Heq.
      apply WD_Expr.
      intros n Hse.
      inversion Hse; subst; inversion H.
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
        apply WD_Expr.
        intros n Hse.
        apply subexpr_var_ibinop in Hse.
        destruct Hse as [Hse | Hse].
        {
          assert(L : well_defined_smt_expr se1 syms).
          { apply IHe1. reflexivity. }
          inversion L; subst.
          apply H.
          assumption.
        }
        {
          assert(L : well_defined_smt_expr se2 syms).
          { apply IHe2. reflexivity. }
          inversion L; subst.
          apply H.
          assumption.
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
        apply WD_Expr.
        intros n Hse.
        apply subexpr_var_icmp in Hse.
        destruct Hse as [Hse | Hse].
        {
          assert(L : well_defined_smt_expr se1 syms).
          { apply IHe1. reflexivity. }
          inversion L; subst.
          apply H.
          assumption.
        }
        {
          assert(L : well_defined_smt_expr se2 syms).
          { apply IHe2. reflexivity. }
          inversion L; subst.
          apply H.
          assumption.
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
      apply WD_Expr.
      intros n Hse.
      assert(L : well_defined_smt_expr se' syms).
      { apply IHe. reflexivity. }
      inversion L; subst.
      apply H.
      apply (subexpr_var_conv n conv se' t1 t2 se); assumption.
    }
    { discriminate Heq. }
  }
  { discriminate Heq. }
Qed.

Lemma well_defined_sym_eval_phi_args : forall s t args pbid se,
  well_defined s ->
  (sym_eval_phi_args (sym_store s) (sym_globals s) t args pbid) = Some se ->
  well_defined_smt_expr se (sym_symbolics s).
Proof.
  intros s t args pbid se Hwd Heq.
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
      inversion Hwd; subst.
      destruct H as [H_1 [H_2 [H_3 H_4]]].
      apply (well_defined_sym_eval_exp
        ls
        gs
        (Some t)
        e
        se
        syms
      ); assumption.
    }
    {
      apply IHargs in Heq.
      assumption.
    }
  }
Qed.

Lemma well_defined_fill_smt_store : forall ls gs l r syms,
  well_defined_smt_store ls syms ->
  well_defined_smt_store gs syms ->
  fill_smt_store ls gs l = Some r ->
  well_defined_smt_store r syms.
Proof.
  intros ls gs l r syms Hwdl Hwdg Heq.
  generalize dependent r.
  induction l as [ | (x, arg) tail]; intros r Heq.
  {
    simpl in Heq.
    inversion Heq; subst.
    apply well_defined_empty_smt_store.
  }
  {
    simpl in Heq.
    destruct arg, t.
    destruct (sym_eval_exp ls gs (Some t) e) as [se | ] eqn:Eeval.
    {
      destruct (fill_smt_store ls gs tail) as [r' | ]  eqn:Efs.
      {
        inversion Heq; subst.
        apply well_defined_smt_store_update.
        {
          apply (IHtail r').
          reflexivity.
        }
        {
          apply (well_defined_sym_eval_exp
            ls
            gs
            (Some t)
            e
            se
            syms
          ); assumption.
        }
      }
      { discriminate Heq. }
    }
    { discriminate Heq. }
  }
Qed.
 
Lemma well_defined_create_local_smt_store : forall d ls gs args r syms,
  well_defined_smt_store ls syms ->
  well_defined_smt_store gs syms ->
  (create_local_smt_store d ls gs args) = Some r ->
  well_defined_smt_store r syms.
Proof.
  intros d ls gs args r syms Hls Hgs H.
  unfold create_local_smt_store in H.
  destruct (merge_lists (df_args d) args) eqn:E.
  { apply well_defined_fill_smt_store with (ls := ls) (gs := gs) (l := l); assumption. }
  { discriminate H. }
Qed.

(* TODO: rename *)
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
      apply well_defined_smt_store_update.
      { assumption. }
      {
        apply (well_defined_sym_eval_exp
          ls
          gs
          None
          e
          se
          syms
        ); assumption.
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
      intros x se' Heq.
      destruct (raw_id_eqb x v) eqn:E.
      {
        rewrite raw_id_eqb_eq in E.
        rewrite E in *. clear E.
        rewrite update_map_eq in Heq.
        injection Heq. clear Heq. intros Heq.
        rewrite <- Heq in *. clear Heq.
        apply (well_defined_sym_eval_phi_args
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
          se
        ); assumption.
      }
      {
        inversion Hwd_ls; subst.
        rewrite raw_id_eqb_neq in E.
        rewrite update_map_neq in Heq.
        apply (H x se'); assumption.
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
        apply WD_Expr.
        intros n Hse.
        apply subexpr_var_binop in Hse.
        destruct Hse as [Hse | Hse].
        {
          inversion Hwd_pc; subst.
          apply H.
          assumption.
        }
        {
          assert(L : well_defined_smt_expr se syms).
          {
            apply (well_defined_sym_eval_exp
              ls
              gs
              (Some (TYPE_I 1))
              e
              se
              syms
            ); assumption.
          }
          inversion L; subst.
          apply H.
          assumption.
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
        apply WD_Expr.
        intros n Hse.
        apply subexpr_var_binop in Hse.
        destruct Hse as [Hse | Hse].
        {
          inversion Hwd_pc; subst.
          apply H.
          assumption.
        }
        {
          assert(L : well_defined_smt_expr se syms).
          {
            apply (well_defined_sym_eval_exp
              ls
              gs
              (Some (TYPE_I 1))
              e
              se
              syms
            ); assumption.
          }
          inversion L; subst.
          apply H.
          apply subexpr_var_not in Hse.
          assumption.
        }
      }
    }
  }
  {
    apply WD_State.
    split.
    { apply (well_defined_create_local_smt_store d ls gs args); assumption. }
    {
      split.
      { assumption. }
      {
        split.
        { apply WD_Frame; assumption. }
        { assumption. }
      }
    }
  }
  {
    apply WD_State.
    split.
    { apply (well_defined_create_local_smt_store d ls gs args); assumption. }
    {
      split.
      { assumption. }
      {
        split.
        { apply WD_Frame; assumption. }
        { assumption. }
      }
    }
  }
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
  {
    apply WD_State.
    inversion Hwd_stk; subst.
    split.
    {
      apply well_defined_smt_store_update.
      { assumption. }
      {
        apply (well_defined_sym_eval_exp
          ls
          gs
          (Some t)
          e
          se
          syms
        ); assumption.
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
      {
        split.
        { assumption. }
        apply WD_Expr.
        intros n Hse.
        apply subexpr_var_binop in Hse.
        destruct Hse as [Hse | Hse].
        {
          inversion Hwd_pc; subst.
          apply H.
          assumption.
        }
        {
          assert(L : well_defined_smt_expr se syms).
          {
            apply (well_defined_sym_eval_exp
              ls
              gs
              (Some (TYPE_I 1))
              e
              se
              syms
            ); assumption.
          }
          inversion L; subst.
          apply H.
          assumption.
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
      intros x se' Heq.
      destruct (raw_id_eqb x v) eqn:E.
      {
        rewrite raw_id_eqb_eq in E.
        rewrite E in *. clear E.
        rewrite update_map_eq in Heq.
        injection Heq. clear Heq. intros Heq.
        subst.
        apply WD_Expr.
        intros n Hse.
        inversion Hse; subst; try inversion H0.
        apply in_eq.
      }
      {
        rewrite raw_id_eqb_neq in E.
        rewrite update_map_neq in Heq.
        {
          apply well_defined_smt_expr_ext.
          apply (H x se').
          assumption.
        }
        { symmetry. assumption. }
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
          apply well_defined_smt_expr_ext.
          assumption.
        }
      }
    }
  }
Qed.

Lemma well_defined_multi_sym_step : forall s s',
  (well_defined s) -> (multi_sym_step s s') -> (well_defined s').
Proof.
  intros s s' Hwd Hmse.
  induction Hmse as [s s' | s s' s''].
  { apply well_defined_sym_step with (s := s); assumption. }
  {
    apply well_defined_sym_step with (s := s').
    { apply IHHmse. assumption. }
    { assumption. }
  }
Qed.
