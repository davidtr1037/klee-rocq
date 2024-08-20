From Coq Require Import List.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Completeness.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellDefinedness.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

Inductive tree (X : Type) : Type :=
  | t_leaf (x : X)
  | t_subtree (x : X) (l : list (tree X))
.

Arguments t_leaf {X}.
Arguments t_subtree {X}.

Definition root {X : Type} (t : tree X) : X :=
  match t with
  | t_leaf x => x
  | t_subtree x _ => x
  end
.

Arguments root {X}.

Definition execution_tree := tree sym_state.

Inductive equiv_smt_store : smt_store -> smt_store -> Prop :=
  | EquivSMTSTore : forall (s1 s2 : smt_store),
      (forall x se1 se2,
        ((s1 x) = None /\ (s2 x) = None) \/
        ((s1 x) = Some se1 /\ (s2 x) = Some se2 /\ equiv_smt_expr se1 se2)
      ) -> equiv_smt_store s1 s2
.

Lemma equiv_smt_store_update : forall s1 s2 v se1 se2,
  equiv_smt_store s1 s2 ->
  equiv_smt_expr se1 se2 ->
  equiv_smt_store (v !-> Some se1; s1) (v !-> Some se2; s2).
Proof.
Admitted.

Lemma equiv_sym_eval_exp : forall ls1 gs1 ls2 gs2 ot e se1,
  equiv_smt_store ls1 ls2 ->
  equiv_smt_store gs1 gs2 ->
  sym_eval_exp ls1 gs1 ot e = Some se1 ->
  (exists se2, (sym_eval_exp ls2 gs2 ot e) = Some se2 /\ equiv_smt_expr se1 se2).
Proof.
Admitted.

Lemma equiv_sym_eval_phi_args : forall ls1 gs1 ls2 gs2 t args pbid se1,
  equiv_smt_store ls1 ls2 ->
  equiv_smt_store gs1 gs2 ->
  sym_eval_phi_args ls1 gs1 t args pbid = Some se1 ->
  (exists se2, sym_eval_phi_args ls2 gs2 t args pbid = Some se2 /\ equiv_smt_expr se1 se2).
Proof.
Admitted.

Inductive equiv_sym_frame : sym_frame -> sym_frame -> Prop :=
  | EquivSymFrame : forall s1 s2 ic pbid v,
      equiv_smt_store s1 s2 ->
      equiv_sym_frame (Sym_Frame s1 ic pbid v) (Sym_Frame s2 ic pbid v)
.

Inductive equiv_sym_stack : list sym_frame -> list sym_frame -> Prop :=
  | EquivSymStack_Empty :
      equiv_sym_stack [] []
  | EquivSymStack_NonEmpty : forall f1 stk1 f2 stk2,
      equiv_sym_stack stk1 stk2 ->
      equiv_sym_frame f1 f2 ->
      equiv_sym_stack (f1 :: stk1) (f2 :: stk2)
.

(* TODO: handle syms *)
Inductive equiv_sym_state : sym_state -> sym_state -> Prop :=
  | Sym_State_Equiv : forall ic c cs pbid ls1 stk1 gs1 pc1 ls2 stk2 gs2 pc2 syms mdl,
      equiv_smt_store ls1 ls2 ->
      equiv_sym_stack stk1 stk2 ->
      equiv_smt_store gs1 gs2 ->
      equiv_smt_expr pc1 pc2 ->
      equiv_sym_state
        (mk_sym_state
          ic
          c
          cs
          pbid
          ls1
          stk1
          gs1
          syms
          pc1
          mdl
        )
        (mk_sym_state
          ic
          c
          cs
          pbid
          ls2
          stk2
          gs2
          syms
          pc2
          mdl
        )
.

Lemma equiv_sym_state_symmetry: forall s1 s2,
  equiv_sym_state s1 s2 <-> equiv_sym_state s2 s1.
Proof.
Admitted.

Lemma equiv_sym_state_transitivity: forall s1 s2 s3,
  equiv_sym_state s1 s2 -> equiv_sym_state s2 s3 -> equiv_sym_state s1 s3.
Proof.
Admitted.

Lemma error_equiv_sym_state: forall s1 s2,
  equiv_sym_state s1 s2 -> ~ error_sym_state s1 -> ~ error_sym_state s2.
Proof.
  intros s1 s2 Heq Hes1.
  inversion Heq; subst.
  intros Hes2.
  apply Hes1.
  inversion Hes2; subst.
  apply ESS_Assert with (d := d); assumption.
Qed.

Inductive safe_et_opt : execution_tree -> Prop :=
  | Safe_Leaf_RetVoid: forall ic cid pbid ls gs syms pc mdl,
      safe_et_opt
        (t_leaf
          (mk_sym_state
            ic
            (CMD_Term cid TERM_RetVoid)
            []
            pbid
            ls
            []
            gs
            syms
            pc
            mdl
          )
        )
  | Safe_Leaf_Ret: forall ic cid t e pbid ls gs syms pc mdl,
      safe_et_opt
        (t_leaf
          (mk_sym_state
            ic
            (CMD_Term cid (TERM_Ret (t, e)))
            []
            pbid
            ls
            []
            gs
            syms
            pc
            mdl
          )
        )
  | Safe_Subtree: forall s l,
      ~ error_sym_state s-> (* to avoid an error state with no children *)
      (forall s',
        sym_step s s' ->
        (
          (exists t, (In t l /\ safe_et_opt t /\ equiv_sym_state s' (root t))) \/ 
          (unsat_sym_state s')
        )
      ) -> safe_et_opt (t_subtree s l)
.

Lemma safe_leaf: forall s,
  safe_et_opt (t_leaf s) -> ~ error_sym_state s.
Proof.
  intros s Hs Hess.
  inversion Hs; subst; inversion Hess.
Qed.

Lemma safe_subtree: forall s l,
  safe_et_opt (t_subtree s l) -> ~ error_sym_state s.
Proof.
  intros s l Hs Hess.
  inversion Hs; subst.
  apply H1 in Hess.
  assumption.
Qed.

Lemma safe_single_step: forall s s' l,
  safe_et_opt (t_subtree s l) ->
  sym_step s s' ->
  (
    safe_et_opt (t_leaf s') \/
    (exists so' l', equiv_sym_state s' so' /\ safe_et_opt (t_subtree so' l')) \/
    unsat_sym_state s'
  ).
Proof.
  intros s s' l Hs Hss.
  inversion Hs; subst.
  apply H2 in Hss.
  destruct Hss as [Hss | Hss].
  {
    destruct Hss as [t [Hss_1 [Hss_2 Hss_3]]].
    destruct t as [x | x l'] eqn:E.
    {
      simpl in Hss_3.
      left.
      admit.
    }
    {
      simpl in Hss_3.
      right.
      left.
      admit.
    }
  }
  { right. right. assumption. }
Admitted.

Lemma equiv_sym_state_on_step: forall s1 s1' s2,
  equiv_sym_state s1 s2 ->
  sym_step s1 s1' ->
  (exists s2', sym_step s2 s2' /\ equiv_sym_state s1' s2').
Proof.
  intros s1 s1' s2 Heq Hs1.
  inversion Hs1;
  subst; rename ls into ls1, stk into stk1, gs into gs1, pc into pc1;
  inversion Heq; subst.
  {
    rename se into se1.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    destruct H as [se2 [H_1 H_2]].
    exists (mk_sym_state
      (next_inst_counter ic c)
      c
      cs
      pbid
      (v !-> Some se2; ls2)
      stk2
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_OP; assumption. }
    {
      apply Sym_State_Equiv; try assumption.
      apply equiv_smt_store_update; assumption.
    }
  }
  {
    rename se into se1.
    apply equiv_sym_eval_phi_args with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    destruct H as [se2 [H_1 H_2]].
    exists (mk_sym_state
      (next_inst_counter ic c)
      c
      cs
      (Some pbid)
      (v !-> Some se2; ls2)
      stk2
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_Phi; assumption. }
    {
      apply Sym_State_Equiv; try assumption.
      apply equiv_smt_store_update; assumption.
    }
  }
  {
    exists (mk_sym_state
      (mk_inst_counter (ic_fid ic) tbid (get_cmd_id c))
      c
      cs
      (Some (ic_bid ic))
      ls2
      stk2
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_UnconditionalBr with (d := d) (b := b); assumption. }
    { apply Sym_State_Equiv; try assumption. }
  }
  {
    rename se into se1.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    destruct H as [se2 [H_1 H_2]].
    exists (mk_sym_state
      (mk_inst_counter (ic_fid ic) bid1 (get_cmd_id c))
      c
      cs
      (Some (ic_bid ic))
      ls2
      stk2
      gs2
      syms
      (SMT_BinOp SMT_And pc2 se2)
      mdl
    ).
    split.
    { apply Sym_Step_Br_True with (d := d) (b := b); assumption. }
    {
      apply Sym_State_Equiv; try assumption.
      apply equiv_smt_and; assumption.
    }
  }
  {
    rename se into se1.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    destruct H as [se2 [H_1 H_2]].
    exists (mk_sym_state
      (mk_inst_counter (ic_fid ic) bid2 (get_cmd_id c))
      c
      cs
      (Some (ic_bid ic))
      ls2
      stk2
      gs2
      syms
      (SMT_BinOp SMT_And pc2 (SMT_Not se2))
      mdl
    ).
    split.
    { apply Sym_Step_Br_False with (d := d) (b := b); assumption. }
    {
      apply Sym_State_Equiv; try assumption.
      apply equiv_smt_and; try assumption.
      apply equiv_smt_not.
      assumption.
    }
  }
  {
    rename ls' into ls1'.
    assert(L :
      exists ls2',
        create_local_smt_store d ls2 gs2 args = Some ls2' /\ equiv_smt_store ls1' ls2'
    ).
    { admit. }
    destruct L as [ls2' [L_1 L_2]].
    exists (mk_sym_state
      (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
      c'
      cs'
      None
      ls2'
      ((Sym_Frame ls2 (next_inst_counter ic c) pbid None) :: stk2)
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_VoidCall; assumption. }
    {
      apply Sym_State_Equiv; try assumption.
      apply EquivSymStack_NonEmpty; try assumption.
      apply EquivSymFrame.
      assumption.
    }
  }
  {
    rename ls' into ls1'.
    assert(L :
      exists ls2',
        create_local_smt_store d ls2 gs2 args = Some ls2' /\ equiv_smt_store ls1' ls2'
    ).
    { admit. }
    destruct L as [ls2' [L_1 L_2]].
    exists (mk_sym_state
      (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
      c'
      cs'
      None
      ls2'
      ((Sym_Frame ls2 (next_inst_counter ic c) pbid (Some v)) :: stk2)
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_Call; assumption. }
    {
      apply Sym_State_Equiv; try assumption.
      apply EquivSymStack_NonEmpty; try assumption.
      apply EquivSymFrame.
      assumption.
    }
  }
  {
    rename ls' into ls1'.
    inversion H13; subst.
    rename stk3 into stk2.
    inversion H5; subst.
    rename s2 into ls2'.
    exists (mk_sym_state
      ic'
      c'
      cs'
      pbid'
      ls2'
      stk2
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_RetVoid with (d := d); assumption. }
    { apply Sym_State_Equiv; assumption. }
  }
  {
    rename se into se1.
    rename ls' into ls1'.
    inversion H14; subst.
    rename stk3 into stk2.
    inversion H6; subst.
    rename s2 into ls2'.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H; try assumption.
    destruct H as [se2 [H_1 H_2]].
    exists (mk_sym_state
      ic'
      c'
      cs'
      pbid'
      (v !-> Some se2; ls2')
      stk2
      gs2
      syms
      pc2
      mdl
    ).
    split.
    { apply Sym_Step_Ret with (d := d); assumption. }
    {
      apply Sym_State_Equiv; try assumption.
      apply equiv_smt_store_update; assumption.
    }
  }
  {
    rename se into se1.
    apply equiv_sym_eval_exp with (ls2 := ls2) (gs2 := gs2) in H2; try assumption.
    destruct H2 as [se2 [H2_1 H2_2]].
    exists (mk_sym_state
      (next_inst_counter ic c)
      c
      cs
      pbid
      ls2
      stk2
      gs2
      syms
      (SMT_BinOp SMT_And pc2 se2)
      mdl
    ).
    split.
    { apply Sym_Step_Assume with (d := d); assumption. }
    {
      apply Sym_State_Equiv; try assumption.
      apply equiv_smt_and; assumption.
    }
  }
  { admit. }
Admitted.

Lemma safe_subtree_equiv: forall s1 s2 l,
  equiv_sym_state s1 s2 ->
  safe_et_opt (t_subtree s1 l) ->
  safe_et_opt (t_subtree s2 l).
Proof.
  intros s1 s2 l Heq Hs1.
  inversion Hs1; subst.
  apply Safe_Subtree.
  { apply error_equiv_sym_state with (s1 := s1); assumption. }
  {
    intros s2' Hstep.
    apply equiv_sym_state_on_step with (s1 := s2) (s2 := s1) in Hstep.
    {
      destruct Hstep as [s1' [Hstep_1 Hstep_2]].
      specialize (H2 s1').
      apply H2 in Hstep_1.
      destruct Hstep_1 as [Hstep_1 | Hstep_1].
      {
        destruct Hstep_1 as [t [Hstep_1_1 [Hstep_1_2 Hstep_1_3]]].
        left.
        exists t.
        split.
        { assumption. }
        {
          split.
          { assumption. }
          { apply equiv_sym_state_transitivity with (s2 := s1'); assumption. }
        }
      }
      {
        right.
        inversion Hstep_2; subst.
        inversion Hstep_1; subst.
        apply Unsat_State.
        apply equiv_smt_expr_unsat with (e1 := pc2) (e2 := pc1).
        { apply equiv_smt_expr_symmetry. assumption. }
        { assumption. }
      }
    }
    { apply equiv_sym_state_symmetry. assumption. }
  }
Qed.

Lemma safe_multi_step: forall s s' l,
  safe_et_opt (t_subtree s l) ->
  multi_sym_step s s' ->
  (
    safe_et_opt (t_leaf s') \/
    (exists so' l', equiv_sym_state s' so' /\ safe_et_opt (t_subtree so' l')) \/
    unsat_sym_state s'
  ).
Proof.
  intros s s' l Hs Hss.
  induction Hss as [s s' | s s' s''].
  { apply safe_single_step with (s := s) (l := l); assumption. }
  {
    apply IHHss in Hs.
    destruct Hs as [Hs | [Hs | Hs]].
    { inversion Hs; subst; inversion H. }
    {
      destruct Hs as [so' [l' [Hs_1 Hs_2]]].
      apply safe_single_step with (s := s') (l := l').
      {
        apply safe_subtree_equiv with (s1 := so').
        { apply equiv_sym_state_symmetry. assumption. }
        { assumption. }
      }
      { assumption. }
    }
    {
      right.
      right.
      apply pc_unsat_lemma with (s := s'); assumption.
    }
  }
Qed.

Theorem completeness_via_et: forall mdl d init_s l,
  is_supported_module mdl ->
  (init_sym_state mdl d) = Some init_s ->
  safe_et_opt (t_subtree init_s l) -> 
  is_safe_program mdl d.
Proof.
  intros mdl d init_s l Hism Hinit Hse.
  unfold is_safe_program.
  assert(L0: exists init_c, init_state mdl d = Some init_c).
  { apply (initialization_correspondence mdl d). exists init_s. assumption. }
  destruct L0 as [init_c L0].
  exists init_c.
  split.
  { assumption. }
  {
    intros c Hms.
    assert(L1 :
      (exists init_s s,
        (init_sym_state mdl d) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c)
    ).
    { apply completeness with (init_c :=  init_c); assumption. }
    destruct L1 as [init_s' [s [L1_1 [L1_2 L1_3]]]].
    rewrite L1_1 in Hinit.
    inversion Hinit; subst.
    (* TODO: rename L *)
    assert(L :
      safe_et_opt (t_leaf s) \/
      (exists so l', equiv_sym_state s so /\ safe_et_opt (t_subtree so l')) \/
      unsat_sym_state s
    ).
    { apply (safe_multi_step init_s s l); assumption. }
    (* TODO: can use same names for lemmas *)
    destruct L as [L | [L | L]].
    {
      assert(L2: ~ error_sym_state s).
      { apply safe_leaf. assumption. }
      intros Hes.
      apply error_correspondence in L1_3.
      apply L1_3 in Hes.
      apply L2.
      assumption.
    }
    {
      destruct L as [so [l' [L_1 L_2]]].
      assert(L3: ~ error_sym_state s).
      {
        apply error_equiv_sym_state with (s1 := so) (s2 := s).
        { apply equiv_sym_state_symmetry. assumption. }
        { apply safe_subtree with (l := l'). assumption. }
      }
      intros Hes.
      apply error_correspondence in L1_3.
      apply L1_3 in Hes.
      apply L3.
      assumption.
    }
    {
      inversion L1_3; subst.
      destruct H as [m H].
      inversion H; subst.
      inversion L; subst.
      unfold unsat in H5.
      destruct H5.
      unfold sat.
      exists m.
      unfold sat_via.
      assumption.
    }
  }
Qed.
