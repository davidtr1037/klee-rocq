From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Relation.

From SE.Utils Require Import IDMap.
From SE.Utils Require Import Util.

Inductive store_has_no_poison : dv_store -> Prop :=
  | Store_Has_No_Poison : forall ls,
      (forall x, (ls x) <> Some DV_Poison) ->
      store_has_no_poison ls
.

Inductive frame_has_no_poison : frame -> Prop :=
  | Frame_Has_No_Poison : forall ls ic pbid v,
      store_has_no_poison ls ->
      frame_has_no_poison (Frame ls ic pbid v)
.

Inductive stack_has_no_poison : list frame -> Prop :=
  | Stack_Has_No_Poison : forall stk,
      (forall f, In f stk -> frame_has_no_poison f) ->
      stack_has_no_poison stk
.

Inductive has_no_poison : state -> Prop :=
  | Has_No_Poison : forall ic c cs pbid ls stk gs mdl,
      store_has_no_poison ls ->
      store_has_no_poison gs ->
      stack_has_no_poison stk ->
      has_no_poison
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

Lemma has_no_poison_store_update : forall s x dv,
  store_has_no_poison s ->
  dv <> DV_Poison ->
  store_has_no_poison (x !-> Some dv; s).
Proof.
  intros s x dv Hnp Hneq.
  apply Store_Has_No_Poison.
  intros y.
  destruct (raw_id_eqb x y) eqn:E.
  {
    rewrite raw_id_eqb_eq in E.
    rewrite E.
    rewrite update_map_eq.
    intros Hf.
    inversion Hf; subst.
    apply Hneq.
    reflexivity.
  }
  {
    rewrite (raw_id_eqb_neq x y) in E.
    rewrite update_map_neq; try assumption.
    inversion Hnp; subst.
    apply H.
  }
Qed.

(* TODO: rename *)
Lemma stack_has_no_poison_suffix : forall f stk,
  stack_has_no_poison (f :: stk) -> stack_has_no_poison stk.
Proof.
  intros f stk H.
  inversion H; subst.
  apply Stack_Has_No_Poison.
  intros f' Hin.
  apply H0.
  apply in_cons.
  assumption.
Qed.

(* TODO: s1 should not contain poison? *)
Inductive ns_step : state -> state -> Prop :=
  | NS_Step : forall s1 s2,
      step s1 s2 -> has_no_poison s2 -> ns_step s1 s2
.

Definition multi_ns_step := multi ns_step.

Lemma ns_step_soundness : forall s1 s2,
  ns_step s1 s2 -> step s1 s2.
Proof.
  intros s1 s2 Hstep.
  inversion Hstep; subst.
  assumption.
Qed.

Lemma multi_ns_step_soundness : forall s1 s2,
  multi_ns_step s1 s2 -> multi_step s1 s2.
Proof.
  intros s1 s2 Hms.
  induction Hms as [s s' | s s' s''].
  {
    apply multi_base.
    apply ns_step_soundness.
    assumption.
  }
  {
    apply multi_trans with (y := s').
    { assumption. }
    { apply ns_step_soundness. assumption. }
  }
Qed.

Lemma has_no_poison_multi_ns_step : forall s1 s2,
  multi_ns_step s1 s2 ->
  has_no_poison s2.
Proof.
  intros s1 s2 Hms.
  inversion Hms; subst.
  { inversion H; subst. assumption. }
  { inversion H0; subst. assumption. }
Qed.

Lemma has_no_poison_eval_exp : forall ls gs ot e dv,
  is_supported_exp e ->
  store_has_no_poison ls ->
  store_has_no_poison gs ->
  eval_exp ls gs ot e = Some dv ->
  dv <> DV_Poison.
Proof.
  intros ls gs ot e dv His Hnp_ls Hnp_gs Heval.
  generalize dependent dv.
  generalize dependent ot.
  induction e; intros ot dv Heval; inversion His; subst; simpl in Heval.
  {
    unfold eval_ident in Heval.
    destruct ot as [t | ] eqn:Eot.
    {
      destruct (lookup_ident ls gs id) as [dv' | ] eqn:E; try discriminate Heval.
      destruct t; try discriminate Heval.
      repeat (
        destruct w;
        try discriminate Heval;
        try (
          destruct dv'; try discriminate Heval;
          destruct di; (inversion Heval; subst; discriminate)
        )
      ).
    }
    {
      unfold lookup_ident in Heval.
      destruct id.
      {
        inversion Hnp_gs.
        specialize (H id).
        rewrite Heval in H.
        apply injection_some_neq.
        assumption.
      }
      {
        inversion Hnp_ls.
        specialize (H id).
        rewrite Heval in H.
        apply injection_some_neq.
        assumption.
      }
    }
  }
  {
    destruct ot; try discriminate Heval.
    destruct t eqn:Et; try discriminate Heval.
    repeat (
      destruct w; (
        simpl in Heval;
        try discriminate Heval;
        try (inversion Heval; subst; intros Hf; discriminate Hf)
      )
    ).
  }
  {
    destruct
      (eval_exp ls gs (Some t) e1) as [dv1 | ] eqn:E1,
      (eval_exp ls gs (Some t) e2) as [dv2 | ] eqn:E2;
    try discriminate Heval.
    apply IHe1 with (dv := dv1) (ot := Some t) in H2; try assumption.
    apply IHe2 with (dv := dv2) (ot := Some t) in H4; try assumption.
    unfold eval_ibinop in Heval.
    destruct dv1 as [di1 | | ] eqn:Edv1, dv2 as [di2 | | ] eqn:Edv2;
    try (discriminate Heval);
    try (destruct di1; discriminate Heval);
    try (destruct H2; reflexivity);
    try (destruct H4; reflexivity).
    destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2];
    try discriminate Heval; (
      unfold eval_ibinop_generic in Heval;
      inversion H5; subst; (
        simpl in Heval;
        intros Hf;
        subst;
        discriminate Heval
      )
    ).
  }
  {
    destruct
      (eval_exp ls gs (Some t) e1) as [dv1 | ] eqn:E1,
      (eval_exp ls gs (Some t) e2) as [dv2 | ] eqn:E2;
    try discriminate Heval.
    apply IHe1 with (dv := dv1) (ot := Some t) in H1; try assumption.
    apply IHe2 with (dv := dv2) (ot := Some t) in H4; try assumption.
    unfold eval_icmp in Heval.
    destruct dv1 as [di1 | | ] eqn:Edv1, dv2 as [di2 | | ] eqn:Edv2;
    try (discriminate Heval);
    try (destruct di1; discriminate Heval);
    try (destruct H1; reflexivity);
    try (destruct H4; reflexivity).
    destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2];
    try discriminate Heval; (
      unfold eval_icmp_generic in Heval;
      intros Hf;
      subst;
      discriminate Heval
    ).
  }
  {
    destruct (eval_exp ls gs (Some t1) e) as [dv' | ] eqn:E;
    try discriminate Heval.
    apply IHe with (dv := dv') (ot := Some t1) in H4; try assumption.
    unfold convert in Heval.
    destruct conv.
    (* Trunc *)
    {
      destruct t1 as [w1 | | | ] eqn:Et1;
      try (
        destruct dv'; try discriminate Heval;
        destruct H4;
        reflexivity
      ).
      repeat (
        destruct w1;
        try (
          destruct dv'; try discriminate Heval;
          destruct H4;
          reflexivity
        )
      );
      (
        destruct dv' eqn:Edv'; [
          destruct di; try discriminate Heval;
          destruct t2 as [w2 | | | ]; try discriminate Heval;
          repeat (
            destruct w2;
            try discriminate Heval;
            try (inversion Heval; subst; intros Hf; discriminate Hf)
          ) |
          discriminate Heval |
          inversion Heval; subst; destruct H4; reflexivity
        ]
      ).
    }
    (* TODO: similar *)
    { admit. }
    { admit. }
    {
      destruct t1 as [w1 | | | ] eqn:Et1, t2 as [w2 | | | ] eqn:Et2; try discriminate Heval.
      destruct (BinPos.Pos.eqb w1 w2) eqn:Ew.
      {
        inversion Heval; subst.
        assumption.
      }
      { discriminate Heval. }
    }
  }
Admitted.

Lemma has_no_poison_eval_phi_args : forall ls gs t args pbid dv,
  (forall bid e, In (bid, e) args -> is_supported_exp e) ->
  store_has_no_poison ls ->
  store_has_no_poison gs ->
  eval_phi_args ls gs t args pbid = Some dv ->
  dv <> DV_Poison.
Proof.
  intros ls gs t args pbid dv His Hnp_ls Hnp_gs Heval.
  generalize dependent dv.
  induction args as [ | arg tail]; intros dv Heval.
  {
    simpl in Heval.
    discriminate.
  }
  {
    simpl in Heval.
    destruct arg as (bid, e).
    destruct (raw_id_eqb bid pbid) eqn:E.
    {
      apply has_no_poison_eval_exp with (ls := ls) (gs := gs) (ot := Some t) (e := e);
      try assumption.
      apply (His bid e).
      apply in_eq.
    }
    {
      apply IHtail.
      {
        intros bid' e' Hin.
        apply (His bid').
        apply in_cons.
        assumption.
      }
      { assumption. }
    }
  }
Qed.

Lemma has_no_poison_empty_store : store_has_no_poison empty_dv_store.
Proof.
  apply Store_Has_No_Poison.
  intros x.
  unfold empty_dv_store.
  rewrite apply_empty_map.
  discriminate.
Qed.

Lemma has_no_poison_fill_store : forall ls gs l ls',
  store_has_no_poison ls ->
  store_has_no_poison gs ->
  (forall x arg, In (x, arg) l -> is_supported_function_arg arg) ->
  fill_store ls gs l = Some ls' ->
  store_has_no_poison ls'.
Proof.
  intros ls gs l ls' Hls Hgs His Heq.
  generalize dependent ls'.
  induction l as [ | (x, arg) tail].
  {
    intros ls' Heq.
    simpl in Heq.
    inversion Heq; subst.
    apply has_no_poison_empty_store.
  }
  {
    intros ls' Heq.
    simpl in Heq.
    destruct arg as [(t, e) attrs].
    destruct (eval_exp ls gs (Some t) e) eqn:Ee; try discriminate.
    destruct (fill_store ls gs tail) eqn:Etail.
    {
      rename d0 into lstail, d into dv.
      inversion Heq; subst.
      apply has_no_poison_store_update.
      {
        apply IHtail.
        {
          intros x' arg' Hin.
          apply (His x').
          apply in_cons.
          assumption.
        }
        { reflexivity. }
      }
      {
        apply has_no_poison_eval_exp with (ls := ls) (gs := gs) (ot := Some t) (e := e);
        try assumption.
        assert(L : is_supported_function_arg (t, e, attrs)).
        { eapply His. apply in_eq. }
        inversion L; subst.
        assumption.
      }
    }
    { discriminate. }
  }
Qed.

Lemma has_no_poison_local_store : forall d ls gs args ls',
  store_has_no_poison ls ->
  store_has_no_poison gs ->
  (forall arg, In arg args -> is_supported_function_arg arg) ->
  create_local_store d ls gs args = Some ls' ->
  store_has_no_poison ls'.
Proof.
  intros d ls gs args ls' Hls Hgs His Heq.
  unfold create_local_store in Heq.
  destruct (ListUtil.merge_lists (df_args d)) eqn:E.
  {
    apply has_no_poison_fill_store with (ls := ls) (gs := gs) (l := l); try assumption.
    apply ListUtil.merge_lists_preserves_prop with (xs := (df_args d)) (ys := args); assumption.
  }
  { discriminate. }
Qed.

Lemma has_no_poison_init_state : forall mdl fid s,
  init_state mdl fid = Some s ->
  has_no_poison s.
Proof.
  intros mdl fid s Hinit.
  unfold init_state in Hinit.
  destruct (find_function mdl fid) as [d | ] eqn:Ed; try discriminate Hinit.
  destruct (build_inst_counter mdl d) as [ic | ] eqn:Eic; try discriminate Hinit.
  destruct (entry_block d) as [b | ] eqn:Eb; try discriminate Hinit.
  destruct (blk_cmds b) as [ | cmd cmds ] eqn:Ecs; try discriminate Hinit.
  inversion Hinit; subst.
  apply Has_No_Poison.
  { apply has_no_poison_empty_store. }
  { apply has_no_poison_empty_store. }
  {
    apply Stack_Has_No_Poison.
    intros f Hin.
    inversion Hin.
  }
Qed.

Lemma has_no_poison_step : forall s1 s2,
  is_supported_state s1 ->
  safe_state ns_step s1 ->
  has_no_poison s1 ->
  step s1 s2 ->
  has_no_poison s2.
Proof.
  intros s1 s2 His Hsafe Hnp Hstep.
  inversion His; subst.
  inversion Hnp; subst.
  inversion Hstep; subst.
  (* INSTR_Op *)
  {
    apply Has_No_Poison; try assumption.
    apply has_no_poison_store_update; try assumption.
    inversion H; subst.
    {
      apply has_no_poison_eval_exp with (ls := ls) (gs := gs) (ot := None) (e := e);
      try eassumption.
    }
    {
      inversion H6; subst.
      (* UDiv *)
      {
        simpl in H14.
        destruct
          (eval_exp ls gs (Some (TYPE_I w)) e1) as [dv1 | ] eqn:E1,
          (eval_exp ls gs (Some (TYPE_I w)) e2) as [dv2 | ] eqn:E2;
        try discriminate H14.
        unfold eval_ibinop in H14.
        destruct dv1 as [di1 | | ] eqn:Edv1, dv2 as [di2 | | ] eqn:Edv2;
        try (discriminate H14);
        try (destruct di1; discriminate H14);
        try (
          apply has_no_poison_eval_exp with (ls := ls) (gs := gs) (ot := Some (TYPE_I w)) (e := e1);
          try assumption;
          rewrite H14 in E1;
          assumption
        ).
        destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2];
        try discriminate H14;
        (
          unfold eval_ibinop_generic in H14;
          destruct ((unsigned n2) =? 0)%Z eqn:E; subst; [
            discriminate H14 |
            simpl in H14;
            inversion H14; subst;
            intros Hf;
            discriminate Hf
          ]
        ).
      }
      (* SDiv *)
      { admit. }
      (* Shl *)
      {
        simpl in H14.
        destruct
          (eval_exp ls gs (Some (TYPE_I w)) e1) as [dv1 | ] eqn:E1,
          (eval_exp ls gs (Some (TYPE_I w)) e2) as [dv2 | ] eqn:E2;
        try discriminate H14.
        unfold eval_ibinop in H14.
        destruct dv1 as [di1 | | ] eqn:Edv1, dv2 as [di2 | | ] eqn:Edv2;
        try (discriminate H14);
        try (destruct di1; discriminate H14);
        try (
          apply has_no_poison_eval_exp
            with (ls := ls) (gs := gs) (ot := Some (TYPE_I w)) (e := e1);
          try assumption;
          rewrite H14 in E1;
          assumption
        );
        try (
          apply has_no_poison_eval_exp
            with (ls := ls) (gs := gs) (ot := Some (TYPE_I w)) (e := e2) (dv := DV_Poison) in H8;
          try assumption;
          destruct H8;
          reflexivity
        ).
        destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2];
        try discriminate H14.
        {
          simpl in H14.
          destruct ((Int1.unsigned n2) >=? 1)%Z eqn:E.
          {
            simpl in H14.
            inversion Hsafe.
            destruct H2.
            eapply ES_Shl; try eassumption.
            simpl.
            unfold Int1.ltu.
            rewrite Int1.unsigned_repr_eq.
            replace (1 mod Int1.modulus)%Z with (1%Z); try reflexivity.
            rewrite Z.geb_ge in E.
            apply Coqlib.zlt_false with (A := bool) (a := true) (b := false) in E.
            rewrite E.
            reflexivity.
          }
          {
            inversion H14; subst.
            discriminate.
          }
        }
        (* TODO: similar *)
        { admit. }
        { admit. }
        { admit. }
        { admit. }
      }
    }
  }
  (* Phi *)
  {
    apply Has_No_Poison; try assumption.
    apply has_no_poison_store_update; try assumption.
    apply has_no_poison_eval_phi_args
      with (ls := ls) (gs := gs) (t := t) (args := args) (pbid := pbid0); try assumption.
    inversion H; subst.
    assumption.
  }
  (* TERM_UnconditionalBr *)
  {
    apply Has_No_Poison; assumption.
  }
  {
    apply Has_No_Poison; assumption.
  }
  {
    apply Has_No_Poison; assumption.
  }
  {
    apply Has_No_Poison.
    {
      apply has_no_poison_local_store with (d := d) (ls := ls) (gs := gs) (args := args);
      try assumption.
      inversion His; subst.
      inversion H; subst.
      assumption.
    }
    { assumption. }
    {
      apply Stack_Has_No_Poison.
      intros f' Hin.
      inversion Hin; subst.
      {
        apply Frame_Has_No_Poison.
        assumption.
      }
      {
        inversion H12; subst.
        apply H3.
        assumption.
      }
    }
  }
  {
    apply Has_No_Poison.
    {
      apply has_no_poison_local_store with (d := d) (ls := ls) (gs := gs) (args := args);
      try assumption.
      inversion His; subst.
      inversion H; subst.
      assumption.
    }
    { assumption. }
    {
      apply Stack_Has_No_Poison.
      intros f' Hin.
      inversion Hin; subst.
      {
        apply Frame_Has_No_Poison.
        assumption.
      }
      {
        inversion H12; subst.
        apply H3.
        assumption.
      }
    }
  }
  {
    apply Has_No_Poison; try assumption.
    {
      assert(L : frame_has_no_poison (Frame ls' ic' pbid' None)).
      {
        inversion H12; subst.
        eapply H2.
        apply in_eq.
      }
      { inversion L; subst. assumption. }
    }
    {
      eapply stack_has_no_poison_suffix.
      eassumption.
    }
  }
  {
    apply Has_No_Poison; try assumption.
    {
      apply has_no_poison_store_update.
      {
        assert(L : frame_has_no_poison (Frame ls' ic' pbid' (Some v))).
        {
          inversion H12; subst.
          eapply H2.
          apply in_eq.
        }
        inversion L; subst.
        assumption.
      }
      {
        apply has_no_poison_eval_exp with (ls := ls) (gs := gs) (ot := Some t) (e := e);
        try assumption.
        { inversion H; subst. assumption. }
      }
    }
    {
      eapply stack_has_no_poison_suffix.
      eassumption.
    }
  }
  {
    apply Has_No_Poison; try assumption.
    apply Store_Has_No_Poison.
    intros x.
    destruct (raw_id_eqb x v) eqn:E.
    {
      rewrite raw_id_eqb_eq in E.
      rewrite E.
      rewrite update_map_eq.
      intros Hf.
      discriminate Hf.
    }
    {
      rewrite raw_id_eqb_neq in E.
      rewrite update_map_neq.
      { inversion H5; subst. apply H2. }
      { symmetry. assumption. }
    }
  }
  {
    apply Has_No_Poison; try assumption.
  }
Admitted.

Lemma ns_step_relative_completeness : forall s1 s2,
  is_supported_state s1 ->
  safe_state ns_step s1 ->
  has_no_poison s1 ->
  step s1 s2 ->
  ns_step s1 s2.
Proof.
  intros s1 s2 His Hsafe Hnp Hstep.
  apply NS_Step.
  { assumption. }
  { apply has_no_poison_step with (s1 := s1); try assumption. }
Qed.

Lemma multi_ns_step_relative_completeness : forall s1 s2,
  is_supported_state s1 ->
  safe_state ns_step s1 ->
  has_no_poison s1 ->
  multi_step s1 s2 ->
  multi_ns_step s1 s2.
Proof.
  intros s1 s2 His Hsafe Hnp Hms.
  induction Hms as [s s' | s s' s''].
  {
    apply ns_step_relative_completeness with (s2 := s') in Hsafe; try assumption.
    apply multi_base.
    assumption.
  }
  {
    assert(Ls' : safe_state ns_step s').
    {
      apply safe_state_preserved_on_reachability with (s := s).
      { assumption. }
      { apply IHHms; assumption. }
    }
    apply multi_trans with (y := s').
    { apply IHHms; assumption. }
    {
      apply ns_step_relative_completeness with (s2 := s'') in Ls'; try assumption.
      { apply is_supported_multi_step with (s := s); assumption. }
      {
        apply has_no_poison_multi_ns_step with (s1 := s).
        apply IHHms; assumption.
      }
    }
  }
Qed.
