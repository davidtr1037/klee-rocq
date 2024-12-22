From Coq Require Import Bool.
From Coq Require Import Lia.
From Coq Require Import List.
From Coq Require Import Logic.Eqdep.
From Coq Require Import String.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import ChoiceAxiom.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import LLVMUtils.
From SE Require Import ModuleAssumptions.
From SE Require Import NonSpeculativeConcrete.
From SE Require Import Symbolic.
From SE Require Import Relation.
From SE Require Import WellScopedness.

From SE.Numeric Require Import Integers.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

(* TODO: fix namespace issues *)
From SE.Utils Require Import IDMap.
From SE.Utils Require StringMap.
From SE.Utils Require ListUtil.

Lemma infer_width : forall s (ast : smt_ast s) w n,
  Some (Expr s ast) = make_smt_const w n -> w = (smt_sort_to_width s).
Proof.
  intros s ast w n H.
  destruct s;
  (
    repeat (destruct w; try (simpl in H; discriminate H));
    reflexivity
  ).
Qed.

Definition repr_by_sort s n : (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.repr n
  | Sort_BV8 => Int8.repr n
  | Sort_BV16 => Int16.repr n
  | Sort_BV32 => Int32.repr n
  | Sort_BV64 => Int64.repr n
  end
.

Definition dynamic_int_by_sort s (n : smt_sort_to_int_type s) : dynamic_int :=
  let f :=
    match s return smt_sort_to_int_type s -> dynamic_int with
    | Sort_BV1 => DI_I1
    | Sort_BV8 => DI_I8
    | Sort_BV16 => DI_I16
    | Sort_BV32 => DI_I32
    | Sort_BV64 => DI_I64
    end in
  f n
.

(* TODO: remove? *)
Lemma eval_udiv_correspondence : forall m s (ast : smt_ast s) n,
  ((n mod (two_power_nat (Pos.to_nat (smt_sort_to_width s)))) <> 0)%Z ->
  over_approx_via_model
    (eval_ibinop
      (UDiv false)
      (DV_Int (dynamic_int_by_sort s (smt_eval_ast m s ast)))
      (DV_Int (dynamic_int_by_sort s (repr_by_sort s n))))
    (Some (Expr s (AST_BinOp s SMT_UDiv ast (AST_Const s (repr_by_sort s n)))))
    m.
Proof.
  intros m s ast n Hn.
  unfold eval_ibinop, eval_ibinop_generic.
  destruct s; simpl.
  {
    rewrite Int1.Z_mod_modulus_eq.
    assert(L : ((n mod Int1.modulus) =? 0)%Z = false).
    {
      apply Z.eqb_neq.
      assumption.
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int8.unsigned_repr_eq.
    assert(L : ((n mod Int8.modulus) =? 0)%Z = false).
    {
      apply Z.eqb_neq.
      assumption.
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int16.Z_mod_modulus_eq.
    assert(L : ((n mod Int16.modulus) =? 0)%Z = false).
    {
      apply Z.eqb_neq.
      assumption.
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int32.unsigned_repr_eq.
    assert(L : ((n mod Int32.modulus) =? 0)%Z = false).
    {
      apply Z.eqb_neq.
      assumption.
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int64.unsigned_repr_eq.
    assert(L : ((n mod Int64.modulus) =? 0)%Z = false).
    {
      apply Z.eqb_neq.
      assumption.
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
Qed.

(* TODO: remove? *)
Lemma eval_sdiv_correspondence : forall m s (ast : smt_ast s) n,
  ((n mod (two_power_nat (Pos.to_nat (smt_sort_to_width s)))) <> 0)%Z ->
  over_approx_via_model
    (eval_ibinop
      (SDiv false)
      (DV_Int (dynamic_int_by_sort s (smt_eval_ast m s ast)))
      (DV_Int (dynamic_int_by_sort s (repr_by_sort s n))))
    (Some (Expr s (AST_BinOp s SMT_SDiv ast (AST_Const s (repr_by_sort s n)))))
    m.
Proof.
  intros m s ast n Hn.
  unfold eval_ibinop, eval_ibinop_generic.
  destruct s; simpl.
  {
    assert(L : (Int1.signed (Int1.repr n) =? 0)%Z = false).
    {
      rewrite Int1.signed_repr_eq.
      remember (Coqlib.zlt (n mod Int1.modulus) Int1.half_modulus) as b.
      assert(L2 : (n mod Int1.modulus < Int1.modulus)%Z).
      {
        apply Z.mod_pos_bound.
        apply Z.ltb_lt.
        reflexivity.
      }
      destruct b eqn:E.
      simpl in *.
      { apply Z.eqb_neq.  assumption. }
      { lia. }
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
  {
    assert(L : (Int8.signed (Int8.repr n) =? 0)%Z = false).
    {
      rewrite Int8.signed_repr_eq.
      remember (Coqlib.zlt (n mod Int8.modulus) Int8.half_modulus) as b.
      assert(L2 : (n mod Int8.modulus < Int8.modulus)%Z).
      {
        apply Z.mod_pos_bound.
        apply Z.ltb_lt.
        reflexivity.
      }
      destruct b eqn:E.
      simpl in *.
      { apply Z.eqb_neq.  assumption. }
      { lia. }
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
  {
    assert(L : (Int16.signed (Int16.repr n) =? 0)%Z = false).
    {
      rewrite Int16.signed_repr_eq.
      remember (Coqlib.zlt (n mod Int16.modulus) Int16.half_modulus) as b.
      assert(L2 : (n mod Int16.modulus < Int16.modulus)%Z).
      {
        apply Z.mod_pos_bound.
        apply Z.ltb_lt.
        reflexivity.
      }
      destruct b eqn:E.
      simpl in *.
      { apply Z.eqb_neq.  assumption. }
      { lia. }
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
  {
    assert(L : (Int32.signed (Int32.repr n) =? 0)%Z = false).
    {
      rewrite Int32.signed_repr_eq.
      remember (Coqlib.zlt (n mod Int32.modulus) Int32.half_modulus) as b.
      assert(L2 : (n mod Int32.modulus < Int32.modulus)%Z).
      {
        apply Z.mod_pos_bound.
        apply Z.ltb_lt.
        reflexivity.
      }
      destruct b eqn:E.
      simpl in *.
      { apply Z.eqb_neq.  assumption. }
      { lia. }
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
  {
    assert(L : (Int64.signed (Int64.repr n) =? 0)%Z = false).
    {
      rewrite Int64.signed_repr_eq.
      remember (Coqlib.zlt (n mod Int64.modulus) Int64.half_modulus) as b.
      assert(L2 : (n mod Int64.modulus < Int64.modulus)%Z).
      {
        apply Z.mod_pos_bound.
        apply Z.ltb_lt.
        reflexivity.
      }
      destruct b eqn:E.
      simpl in *.
      { apply Z.eqb_neq.  assumption. }
      { lia. }
    }
    rewrite L.
    eapply OA_Some; reflexivity.
  }
Qed.

(* TODO: remove? *)
Lemma eval_shl_correspondence : forall m s (ast : smt_ast s) n,
  (n >= 0)%Z ->
  (n < Zpos (smt_sort_to_width s))%Z ->
  over_approx_via_model
    (eval_ibinop (Shl false false)
       (DV_Int (dynamic_int_by_sort s (smt_eval_ast m s ast)))
       (DV_Int (dynamic_int_by_sort s (repr_by_sort s n))))
    (Some (Expr s (AST_BinOp s SMT_Shl ast (AST_Const s (repr_by_sort s n)))))
    m.
Proof.
  intros m s ast n Hn1 Hn2.
  unfold eval_ibinop, eval_ibinop_generic.
  destruct s; unfold bitwidth; simpl in *.
  {
    rewrite Int1.Z_mod_modulus_eq.
    assert(L1 : (n = 0)%Z).
    { lia. }
    subst.
    simpl.
    eapply OA_Some.
    { reflexivity. }
    {
      simpl.
      f_equal.
      apply Int1.shl_zero.
    }
  }
  {
    rewrite Int8.unsigned_repr_eq.
    assert(L1: (n mod Int8.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int8.modulus, Int8.wordsize, Wordsize_8.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 8)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
  {
    (* TODO: why is this case different? *)
    rewrite Int16.Z_mod_modulus_eq.
    assert(L1: (n mod Int16.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int16.modulus, Int16.wordsize, Wordsize_16.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 16)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int32.unsigned_repr_eq.
    assert(L1: (n mod Int32.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int32.modulus, Int32.wordsize, Wordsize_32.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 32)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int64.unsigned_repr_eq.
    assert(L1: (n mod Int64.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 64)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
Qed.

(* TODO: remove? *)
Lemma eval_lshr_correspondence : forall m s (ast : smt_ast s) n,
  (n >= 0)%Z ->
  (n < Zpos (smt_sort_to_width s))%Z ->
  over_approx_via_model
    (eval_ibinop (LShr false)
       (DV_Int (dynamic_int_by_sort s (smt_eval_ast m s ast)))
       (DV_Int (dynamic_int_by_sort s (repr_by_sort s n))))
    (Some (Expr s (AST_BinOp s SMT_LShr ast (AST_Const s (repr_by_sort s n)))))
    m.
Proof.
  intros m s ast n Hn1 Hn2.
  unfold eval_ibinop, eval_ibinop_generic.
  destruct s; unfold bitwidth; simpl in *.
  {
    rewrite Int1.Z_mod_modulus_eq.
    assert(L1 : (n = 0)%Z).
    { lia. }
    subst.
    simpl.
    eapply OA_Some.
    { reflexivity. }
    {
      simpl.
      f_equal.
      apply Int1.shru_zero.
    }
  }
  {
    rewrite Int8.unsigned_repr_eq.
    assert(L1: (n mod Int8.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int8.modulus, Int8.wordsize, Wordsize_8.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 8)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
  {
    (* TODO: why is this case different? *)
    rewrite Int16.Z_mod_modulus_eq.
    assert(L1: (n mod Int16.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int16.modulus, Int16.wordsize, Wordsize_16.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 16)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int32.unsigned_repr_eq.
    assert(L1: (n mod Int32.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int32.modulus, Int32.wordsize, Wordsize_32.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 32)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int64.unsigned_repr_eq.
    assert(L1: (n mod Int64.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 64)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
Qed.

(* TODO: remove? *)
Lemma eval_ashr_correspondence : forall m s (ast : smt_ast s) n,
  (n >= 0)%Z ->
  (n < Zpos (smt_sort_to_width s))%Z ->
  over_approx_via_model
    (eval_ibinop (AShr false)
       (DV_Int (dynamic_int_by_sort s (smt_eval_ast m s ast)))
       (DV_Int (dynamic_int_by_sort s (repr_by_sort s n))))
    (Some (Expr s (AST_BinOp s SMT_AShr ast (AST_Const s (repr_by_sort s n)))))
    m.
Proof.
  intros m s ast n Hn1 Hn2.
  unfold eval_ibinop, eval_ibinop_generic.
  destruct s; unfold bitwidth; simpl in *.
  {
    rewrite Int1.Z_mod_modulus_eq.
    assert(L1 : (n = 0)%Z).
    { lia. }
    subst.
    simpl.
    eapply OA_Some.
    { reflexivity. }
    {
      simpl.
      f_equal.
      apply Int1.shr_zero.
    }
  }
  {
    rewrite Int8.unsigned_repr_eq.
    assert(L1: (n mod Int8.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int8.modulus, Int8.wordsize, Wordsize_8.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 8)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
  {
    (* TODO: why is this case different? *)
    rewrite Int16.Z_mod_modulus_eq.
    assert(L1: (n mod Int16.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int16.modulus, Int16.wordsize, Wordsize_16.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 16)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int32.unsigned_repr_eq.
    assert(L1: (n mod Int32.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int32.modulus, Int32.wordsize, Wordsize_32.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 32)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
  {
    rewrite Int64.unsigned_repr_eq.
    assert(L1: (n mod Int64.modulus)%Z = n).
    {
      apply Z.mod_small.
      split.
      { lia. }
      {
        unfold Int64.modulus, Int64.wordsize, Wordsize_64.wordsize, two_power_nat.
        simpl.
        lia.
      }
    }
    rewrite L1.
    assert(L2 : (n >=? 64)%Z = false).
    { lia. }
    rewrite L2.
    eapply OA_Some; reflexivity.
  }
Qed.
 
(* TODO: rename correspondence to over_approx? *)
Lemma eval_exp_correspondence : forall c_ls s_ls c_gs s_gs ot e m,
  is_supported_exp e ->
  over_approx_store_via s_ls c_ls m ->
  over_approx_store_via s_gs c_gs m ->
  over_approx_via_model (eval_exp c_ls c_gs ot e) (sym_eval_exp s_ls s_gs ot e) m.
Proof.
  intros c_ls s_ls c_gs s_gs ot e m His Hls Hgs.
  generalize dependent ot.
  induction e; intros ot; simpl; try (inversion His; subst).
  (* EXP_Ident *)
  {
    unfold eval_ident, sym_eval_ident.
    destruct ot as [t | ].
    {
      destruct
        (lookup_ident c_ls c_gs id) as [dv | ] eqn:Edv,
        (sym_lookup_ident s_ls s_gs id) as [se | ] eqn:Ese.
      {
        destruct t; try apply OA_None.
        repeat (
          destruct w;
          try apply OA_None;
          try (
            destruct id;
            [
              inversion Hgs; subst;
              specialize (H id);
              unfold lookup_ident, sym_lookup_ident in *;
              rewrite Edv, Ese in H;
              inversion H; subst;
              destruct sort; try apply OA_None;
              simpl;
              assumption |
              inversion Hls; subst;
              specialize (H id);
              unfold lookup_ident, sym_lookup_ident in *;
              rewrite Edv, Ese in H;
              inversion H; subst;
              destruct sort; try apply OA_None;
              simpl;
              assumption
            ]
          )
        ).
      }
      {
        destruct id.
        {
          inversion Hgs; subst.
          specialize (H id).
          unfold lookup_ident, sym_lookup_ident in *.
          rewrite Edv, Ese in H.
          inversion H.
        }
        {
          inversion Hls; subst.
          specialize (H id).
          unfold lookup_ident, sym_lookup_ident in *.
          rewrite Edv, Ese in H.
          inversion H.
        }
      }
      {
        destruct id.
        {
          inversion Hgs; subst.
          specialize (H id).
          unfold lookup_ident, sym_lookup_ident in *.
          rewrite Edv, Ese in H.
          inversion H.
        }
        {
          inversion Hls; subst.
          specialize (H id).
          unfold lookup_ident, sym_lookup_ident in *.
          rewrite Edv, Ese in H.
          inversion H.
        }
      }
      { apply OA_None. }
    }
    {
      destruct id.
      {
        unfold lookup_ident, sym_lookup_ident.
        inversion Hgs; subst.
        apply H.
      }
      {
        unfold lookup_ident, sym_lookup_ident.
        inversion Hls; subst.
        apply H.
      }
    }
  }
  (* EXP_Integer *)
  {
    destruct ot.
    {
      destruct t; try (apply OA_None).
      repeat (destruct w; try (apply OA_None)); (
        eapply OA_Some; reflexivity
      ).
    }
    { apply OA_None. }
  }
  {
    apply IHe1 with (ot := (Some t)) in H2.
    apply IHe2 with (ot := (Some t)) in H4.
    destruct (eval_exp c_ls c_gs (Some t) e1) as [dv1 | ] eqn:E1.
    {
      destruct (eval_exp c_ls c_gs (Some t) e2) as [dv2 | ] eqn:E2.
      {
        inversion H2; subst.
        inversion H4; subst.
        rename sort into sort1, ast into ast1, sort0 into sort2, ast0 into ast2.
        destruct op;
        try (
          inversion H5; (
            destruct sort1, sort2; try (apply OA_None); (
              eapply OA_Some; reflexivity
            )
          )
        ).
      }
      {
        inversion H2; subst.
        inversion H4; subst.
        apply OA_None.
      }
    }
    {
      inversion H2; subst.
      apply OA_None.
    }
  }
  {
    apply IHe1 with (ot := (Some t)) in H1.
    apply IHe2 with (ot := (Some t)) in H4.
    destruct (eval_exp c_ls c_gs (Some t) e1) as [dv1 | ] eqn:E1.
    {
      destruct (eval_exp c_ls c_gs (Some t) e2) as [dv2 | ] eqn:E2.
      {
        inversion H1; subst.
        inversion H4; subst.
        rename sort into sort1, ast into ast1, sort0 into sort2, ast0 into ast2.
        (* TODO: find a better solution! *)
        destruct sort1, sort2; try (apply OA_None).
        {
          eapply OA_Some.
          { reflexivity. }
          {
            simpl.
            unfold smt_eval_cmpop_by_sort.
            unfold smt_eval_cmpop_generic.
            unfold eval_cmp_result.
            simpl.
            replace
              (smt_cmpop_to_comparison (icmp_to_smt_cmpop op)) with (icmp_to_comparison op).
            {
              remember (
                Int1.cmpu
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV1 ast1)
                  (smt_eval_ast m Sort_BV1 ast2)
              ) as bu.
              remember (
                Int1.cmp
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV1 ast1)
                  (smt_eval_ast m Sort_BV1 ast2)
              ) as b.
              destruct op;
              (simpl; destruct bu; destruct b; reflexivity).
            }
            { destruct op; reflexivity. }
          }
        }
        {
          eapply OA_Some.
          { reflexivity. }
          {
            simpl.
            unfold smt_eval_cmpop_by_sort.
            unfold smt_eval_cmpop_generic.
            unfold eval_cmp_result.
            simpl.
            replace
              (smt_cmpop_to_comparison (icmp_to_smt_cmpop op)) with (icmp_to_comparison op).
            {
              remember (
                Int8.cmpu
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV8 ast1)
                  (smt_eval_ast m Sort_BV8 ast2)
              ) as bu.
              remember (
                Int8.cmp
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV8 ast1)
                  (smt_eval_ast m Sort_BV8 ast2)
              ) as b.
              destruct op;
              (simpl; destruct bu; destruct b; reflexivity).
            }
            { destruct op; reflexivity. }
          }
        }
        {
          eapply OA_Some.
          { reflexivity. }
          {
            simpl.
            unfold smt_eval_cmpop_by_sort.
            unfold smt_eval_cmpop_generic.
            unfold eval_cmp_result.
            simpl.
            replace
              (smt_cmpop_to_comparison (icmp_to_smt_cmpop op)) with (icmp_to_comparison op).
            {
              remember (
                Int16.cmpu
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV16 ast1)
                  (smt_eval_ast m Sort_BV16 ast2)
              ) as bu.
              remember (
                Int16.cmp
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV16 ast1)
                  (smt_eval_ast m Sort_BV16 ast2)
              ) as b.
              destruct op;
              (simpl; destruct bu; destruct b; reflexivity).
            }
            { destruct op; reflexivity. }
          }
        }
        {
          eapply OA_Some.
          { reflexivity. }
          {
            simpl.
            unfold smt_eval_cmpop_by_sort.
            unfold smt_eval_cmpop_generic.
            unfold eval_cmp_result.
            simpl.
            replace
              (smt_cmpop_to_comparison (icmp_to_smt_cmpop op)) with (icmp_to_comparison op).
            {
              remember (
                Int32.cmpu
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV32 ast1)
                  (smt_eval_ast m Sort_BV32 ast2)
              ) as bu.
              remember (
                Int32.cmp
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV32 ast1)
                  (smt_eval_ast m Sort_BV32 ast2)
              ) as b.
              destruct op;
              (simpl; destruct bu; destruct b; reflexivity).
            }
            { destruct op; reflexivity. }
          }
        }
        {
          eapply OA_Some.
          { reflexivity. }
          {
            simpl.
            unfold smt_eval_cmpop_by_sort.
            unfold smt_eval_cmpop_generic.
            unfold eval_cmp_result.
            simpl.
            replace
              (smt_cmpop_to_comparison (icmp_to_smt_cmpop op)) with (icmp_to_comparison op).
            {
              remember (
                Int64.cmpu
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV64 ast1)
                  (smt_eval_ast m Sort_BV64 ast2)
              ) as bu.
              remember (
                Int64.cmp
                  (icmp_to_comparison op)
                  (smt_eval_ast m Sort_BV64 ast1)
                  (smt_eval_ast m Sort_BV64 ast2)
              ) as b.
              destruct op;
              (simpl; destruct bu; destruct b; reflexivity).
            }
            { destruct op; reflexivity. }
          }
        }
      }
      {
        inversion H1; subst.
        inversion H4; subst.
        apply OA_None.
      }
    }
    {
      inversion H1; subst.
      apply OA_None.
    }
  }
  {
    apply IHe with (ot := (Some t1)) in H4.
    destruct (eval_exp c_ls c_gs (Some t1) e) as [dv | ] eqn:E.
    {
      (* TODO: avoid duplicate blocks *)
      inversion H1; subst.
      {
        inversion H4; subst.
        destruct t1; try apply OA_None.
        destruct t2;
        try (
          simpl;
          repeat (destruct w; try apply OA_None);
          destruct (make_dynamic_int sort (smt_eval_ast m sort ast)); apply OA_None
        ).
        {
          rename w into w1, w0 into w2.
          repeat (destruct w1; try apply OA_None);
          (
            simpl;
            destruct sort; try apply OA_None;
            (
              repeat (destruct w2; try apply OA_None);
              (
                simpl;
                eapply OA_Some; reflexivity
              )
            )
          ).
        }
      }
      {
        inversion H4; subst.
        destruct t1; try apply OA_None.
        destruct t2;
        try (
          simpl;
          repeat (destruct w; try apply OA_None);
          destruct (make_dynamic_int sort (smt_eval_ast m sort ast)); apply OA_None
        ).
        {
          rename w into w1, w0 into w2.
          repeat (destruct w1; try apply OA_None);
          (
            simpl;
            destruct sort; try apply OA_None;
            (
              repeat (destruct w2; try apply OA_None);
              (
                simpl;
                eapply OA_Some; reflexivity
              )
            )
          ).
        }
      }
      {
        inversion H4; subst.
        destruct t1; try apply OA_None.
        destruct t2;
        try (
          simpl;
          repeat (destruct w; try apply OA_None);
          destruct (make_dynamic_int sort (smt_eval_ast m sort ast)); apply OA_None
        ).
        {
          rename w into w1, w0 into w2.
          repeat (destruct w1; try apply OA_None);
          (
            simpl;
            destruct sort; try apply OA_None;
            (
              repeat (destruct w2; try apply OA_None);
              (
                simpl;
                eapply OA_Some; reflexivity
              )
            )
          ).
        }
      }
      {
        inversion H4; subst.
        destruct t1, t2;
        try apply OA_None.
        simpl.
        rename w into w1, w0 into w2.
        destruct (w1 =? w2)%positive.
        {
          eapply OA_Some.
          { reflexivity. }
          { reflexivity. }
        }
        { apply OA_None. }
      }
    }
    {
      inversion H4; subst.
      apply OA_None.
    }
  }
Qed.

Lemma empty_store_correspondence : forall m,
  over_approx_store_via empty_smt_store empty_dv_store m.
Proof.
  intros m.
  apply OA_Store.
  intros x.
  unfold empty_dv_store, empty_smt_store.
  rewrite apply_empty_map, apply_empty_map.
  apply OA_None.
Qed.

Lemma store_update_correspondence : forall dv se m v c_s s_s,
  over_approx_via_model (Some dv) (Some se) m ->
  over_approx_store_via s_s c_s m ->
  over_approx_store_via (v !-> Some se; s_s) (v !-> Some dv; c_s) m.
Proof.
  intros dv se m v c_s s_s H1 H2.
  apply OA_Store.
  intros x.
  destruct (raw_id_eqb x v) eqn:E.
  {
    rewrite raw_id_eqb_eq in E.
    rewrite E.
    rewrite update_map_eq, update_map_eq.
    assumption.
  }
  {
    rewrite raw_id_eqb_neq in E.
    rewrite update_map_neq, update_map_neq; try (symmetry; assumption).
    inversion H2; subst.
    apply H.
  }
Qed.

Lemma eval_phi_args_correspondence : forall c_ls s_ls c_gs s_gs t args pbid m,
  (forall bid e, In (bid, e) args -> is_supported_exp e) ->
  over_approx_store_via s_ls c_ls m ->
  over_approx_store_via s_gs c_gs m ->
  over_approx_via_model
    (eval_phi_args c_ls c_gs t args pbid)
    (sym_eval_phi_args s_ls s_gs t args pbid)
    m.
Proof.
  intros c_ls s_ls c_gs s_gs t args pbid m His Hoal Hoag.
  induction args as [ | arg args_tail].
  {
    simpl.
    apply OA_None.
  }
  {
    simpl.
    destruct arg as [bid e].
    destruct (raw_id_eqb bid pbid) eqn:E.
    {
      rewrite raw_id_eqb_eq in E.
      apply eval_exp_correspondence; try assumption.
      apply (His bid).
      apply in_eq.
    }
    {
      apply IHargs_tail.
      intros bid' e' Hin.
      apply (His bid').
      apply in_cons.
      assumption.
    }
  }
Qed.

Lemma fill_store_correspondence : forall c_ls s_ls c_gs s_gs m l c_ls',
  over_approx_store_via s_ls c_ls m ->
  over_approx_store_via s_gs c_gs m ->
  (forall x arg, In (x, arg) l -> is_supported_function_arg arg) ->
  fill_store c_ls c_gs l = Some c_ls' ->
  exists s_ls',
    fill_smt_store s_ls s_gs l = Some s_ls' /\ over_approx_store_via s_ls' c_ls' m.
Proof.
  intros c_ls s_ls c_gs s_gs m l c_ls' Hoac Hoag His Hc.
  generalize dependent c_ls'.
  induction l as [ | (x, arg) tail].
  {
    intros c_ls' Hc.
    exists empty_smt_store.
    split.
    { reflexivity. }
    {
      simpl in Hc.
      inversion Hc; subst.
      apply empty_store_correspondence.
    }
  }
  {
    intros c_ls' Hc.
    simpl in Hc.
    destruct arg as [y attrs]. destruct y.
    assert(L :
      over_approx_via_model
        (eval_exp c_ls c_gs (Some t) e)
        (sym_eval_exp s_ls s_gs (Some t) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      specialize (His x ((t, e), attrs)).
      assert(Larg : is_supported_function_arg ((t, e), attrs)).
      { apply His. apply in_eq. }
      inversion Larg; subst.
      assumption.
    }
    destruct (eval_exp c_ls c_gs (Some t) e) as [dv | ] eqn:Eeval.
    {
      destruct (fill_store c_ls c_gs tail) as [c_ls'' | ] eqn:Efc.
      {
        assert(L2 :
          forall c_ls',
            Some c_ls'' = Some c_ls' ->
            exists s_ls' : smt_store,
              fill_smt_store s_ls s_gs tail = Some s_ls' /\
              over_approx_store_via s_ls' c_ls' m
        ).
        {
          apply IHtail.
          intros x' arg' Hin.
          apply (His x' arg').
          apply in_cons.
          assumption.
        }
        specialize (L2 c_ls'').
        destruct L2 as [s_ls'' L2].
        { reflexivity. }
        {
          destruct L2 as [L2_1 L2_2].
          inversion L; subst.
          exists (x !-> Some (Expr sort ast); s_ls'').
          split.
          {
            simpl.
            rewrite <- H0.
            rewrite L2_1.
            reflexivity.
          }
          {
            inversion Hc; subst.
            apply store_update_correspondence; try assumption.
            eapply OA_Some; reflexivity.
          }
        }
      }
      { inversion Hc. }
    }
    { discriminate Hc. }
  }
Qed.

Lemma create_local_store_correspondence : forall d c_ls c_gs s_ls s_gs m args c_ls',
  over_approx_store_via s_ls c_ls m ->
  over_approx_store_via s_gs c_gs m ->
  (forall arg, In arg args -> is_supported_function_arg arg) ->
  create_local_store d c_ls c_gs args = Some c_ls' ->
  exists s_ls',
    create_local_smt_store d s_ls s_gs args = Some s_ls' /\
    over_approx_store_via s_ls' c_ls' m.
Proof.
  intros d c_ls c_gs s_ls s_gs m args c_ls' Hoal Hoag His Hc.
  unfold create_local_store in Hc.
  unfold create_local_smt_store.
  destruct (ListUtil.merge_lists (df_args d)) eqn:E.
  {
    apply fill_store_correspondence with (c_ls := c_ls) (c_gs := c_gs); try assumption.
    apply ListUtil.merge_lists_preserves_prop with (xs := (df_args d)) (ys := args);
    assumption.
  }
  { discriminate Hc. }
Qed.

(* TODO: rename *)
Lemma LX0 : forall s x se name syms,
  well_scoped_smt_store s syms ->
  ~ In name syms ->
  s x = Some se ->
  ~ contains_var se name.
Proof.
  intros s x se name syms Hws Hin Heq.
  inversion Hws; subst.
  specialize (H x se).
  apply H in Heq.
  inversion Heq; subst.
  specialize (H0 name).
  intros Hse.
  apply H0 in Hse.
  apply Hin in Hse.
  assumption.
Qed.

Lemma over_approx_store_non_interference : forall s_s c_s m name n syms,
  over_approx_store_via s_s c_s m ->
  well_scoped_smt_store s_s syms ->
  ~ In name syms ->
  over_approx_store_via
    s_s
    c_s
    (mk_smt_model (StringMap.update_map (bv_model m) name n)).
Proof.
  intros s_s c_s m name n syms Hoa Hws Hin.
  apply OA_Store.
  intros x.
  inversion Hoa; subst.
  specialize (H x).
  inversion H; subst.
  { apply OA_None. }
  {
    eapply OA_Some; try reflexivity.
    rewrite <- subexpr_non_interference with (x := name) (n := n).
    { reflexivity. }
    {
      apply (LX0 s_s x (Expr sort ast) name syms); try assumption.
      symmetry.
      assumption.
    }
  }
Qed.

Lemma over_approx_stack_non_interference : forall s_stk c_stk m name n syms,
  over_approx_stack_via s_stk c_stk m ->
  well_scoped_stack s_stk syms ->
  ~ In name syms ->
  over_approx_stack_via
    s_stk
    c_stk
    (mk_smt_model (StringMap.update_map (bv_model m) name n))
.
Proof.
  intros s_stk c_stk m name n syms Hoa Hws Hin.
  induction Hoa.
  { apply OA_Stack_Empty. }
  {
    apply OA_Stack_NonEmpty.
    {
      inversion H; subst.
      apply OA_Frame.
      apply over_approx_store_non_interference with (syms := syms); try assumption.
      inversion Hws; subst.
      assumption.
    }
    {
      apply IHHoa.
      inversion Hws; subst; assumption.
    }
  }
Qed.

(* TODO: generalize *)
Lemma infer_sort : forall (sort : smt_sort) (x : smt_sort_to_int_type sort) (n : int1),
  make_dynamic_int sort x = DI_I1 n -> sort = Sort_BV1.
Proof.
  intros sort x n H.
  destruct sort; try ( simpl in H; discriminate H ).
  { reflexivity. }
Qed.

(* TODO: (has_no_poison c) can be inferred from (over_approx s c)? *)
Lemma completeness_single_step :
  forall c c' s,
    is_supported_state c ->
    has_no_poison c ->
    ns_step c c' ->
    well_scoped s ->
    over_approx s c ->
    (exists s', sym_step s s' /\ over_approx s' c').
Proof.
  intros c c' s Hiss Hnp Hs Hws Hoa.
  destruct c as [c_ic c_c c_cs c_pbid c_ls c_stk c_gs c_mdl].
  destruct s as [s_ic s_c s_cs s_pbid s_ls s_stk s_gs s_syms s_pc s_mdl].
  inversion Hs; subst.
  inversion H; subst;
  inversion Hoa; subst;
  destruct H1 as [m H1];
  inversion H1; subst.
  (* INSTR_Op *)
  {
    inversion Hiss; subst.
    inversion Hnp; subst.
    inversion H5; subst.
    {
      assert(L :
        over_approx_via_model
          (eval_exp c_ls c_gs None e)
          (sym_eval_exp s_ls s_gs None e)
          m
      ).
      { apply eval_exp_correspondence; assumption. }
      inversion L; subst.
      { rewrite H10 in *. discriminate H4. }
      {
        exists (mk_sym_state
          (next_inst_counter c_ic c)
          c
          cs
          c_pbid
          (v !-> Some (Expr sort ast); s_ls)
          s_stk
          s_gs
          s_syms
          s_pc
          c_mdl
        ).
        split.
        {
          apply Sym_Step_OP.
          symmetry.
          assumption.
        }
        {
          apply OA_State.
          exists m.
          apply OAV_State; try assumption.
          apply store_update_correspondence.
          {
            rewrite H10 in H2.
            rewrite <- H2.
            eapply OA_Some; reflexivity.
          }
          { assumption. }
        }
      }
    }
    {
      inversion H7; subst.
      (* UDiv *)
      {
        simpl in H10.
        destruct
          (eval_exp c_ls c_gs (Some (TYPE_I w)) e1) as [dv1 | ] eqn:E1,
          (eval_exp c_ls c_gs (Some (TYPE_I w)) e2) as [dv2 | ] eqn:E2;
        try discriminate H10.
        destruct dv1 as [di1 | | ] , dv2 as [di2 | | ];
        try (
          unfold eval_ibinop in H10;
          destruct di1; discriminate H10
        );
        try (
          unfold eval_ibinop in H10;
          destruct di2; discriminate H10
        );
        try (
          unfold eval_ibinop in H10;
          discriminate H10
        );
        try (
          apply has_no_poison_eval_exp in E1; try assumption;
          destruct E1; reflexivity
        ).
        unfold eval_ibinop in H10.
        destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2];
        try (discriminate H10).
        {
          simpl in H10.
          destruct (Int1.unsigned n2 =? 0)%Z eqn:En2; try discriminate H10.
          assert(L1 :
            over_approx_via_model
              (eval_exp c_ls c_gs (Some (TYPE_I w)) e1)
              (sym_eval_exp s_ls s_gs (Some (TYPE_I w)) e1)
              m
          ).
          { apply eval_exp_correspondence; assumption. }
          assert(L2 :
            over_approx_via_model
              (eval_exp c_ls c_gs (Some (TYPE_I w)) e2)
              (sym_eval_exp s_ls s_gs (Some (TYPE_I w)) e2)
              m
          ).
          { apply eval_exp_correspondence; assumption. }
          rewrite E1 in L1.
          rewrite E2 in L2.
          inversion L1; subst.
          inversion L2; subst.
          rename sort into sort1, ast into ast1, sort0 into sort2, ast0 into ast2.
          assert(Lsort1 : sort1 = Sort_BV1).
          { eapply infer_sort. eassumption. }
          assert(Lsort2 : sort2 = Sort_BV1).
          { eapply infer_sort. eassumption. }
          subst.
          exists (mk_sym_state
            (next_inst_counter c_ic c)
            c
            cs
            c_pbid
            (v !-> Some (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_UDiv ast1 ast2)); s_ls)
            s_stk
            s_gs
            s_syms
            s_pc
            c_mdl
          ).
          split.
          {
            apply Sym_Step_OP.
            simpl.
            rewrite <- H3.
            rewrite <- H4.
            reflexivity.
          }
          {
            apply OA_State.
            exists m.
            apply OAV_State; try assumption.
            apply store_update_correspondence.
            {
              rewrite <- H10.
              eapply OA_Some.
              { reflexivity. }
              {
                simpl.
                inversion H11; subst.
                inversion H17; subst.
                reflexivity.
              }
            }
            { assumption. }
          }
        }
        (* TODO: those are similar to the Sort_BV1 case *)
        { admit. }
        { admit. }
        { admit. }
        { admit. }
      }
      (* SDiv *)
      (* TODO: very similar to UDiv *)
      {
        simpl in H10.
        destruct
          (eval_exp c_ls c_gs (Some (TYPE_I w)) e1) as [dv1 | ] eqn:E1,
          (eval_exp c_ls c_gs (Some (TYPE_I w)) e2) as [dv2 | ] eqn:E2;
        try discriminate H10.
        destruct dv1 as [di1 | | ] , dv2 as [di2 | | ];
        try (
          unfold eval_ibinop in H10;
          destruct di1; discriminate H10
        );
        try (
          unfold eval_ibinop in H10;
          destruct di2; discriminate H10
        );
        try (
          unfold eval_ibinop in H10;
          discriminate H10
        );
        try (
          apply has_no_poison_eval_exp in E1; try assumption;
          destruct E1; reflexivity
        ).
        unfold eval_ibinop in H10.
        destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2];
        try (discriminate H10).
        {
          simpl in H10.
          destruct (Int1.signed n2 =? 0)%Z eqn:En2; try discriminate H10.
          assert(L1 :
            over_approx_via_model
              (eval_exp c_ls c_gs (Some (TYPE_I w)) e1)
              (sym_eval_exp s_ls s_gs (Some (TYPE_I w)) e1)
              m
          ).
          { apply eval_exp_correspondence; assumption. }
          assert(L2 :
            over_approx_via_model
              (eval_exp c_ls c_gs (Some (TYPE_I w)) e2)
              (sym_eval_exp s_ls s_gs (Some (TYPE_I w)) e2)
              m
          ).
          { apply eval_exp_correspondence; assumption. }
          rewrite E1 in L1.
          rewrite E2 in L2.
          inversion L1; subst.
          inversion L2; subst.
          rename sort into sort1, ast into ast1, sort0 into sort2, ast0 into ast2.
          assert(Lsort1 : sort1 = Sort_BV1).
          { eapply infer_sort. eassumption. }
          assert(Lsort2 : sort2 = Sort_BV1).
          { eapply infer_sort. eassumption. }
          subst.
          exists (mk_sym_state
            (next_inst_counter c_ic c)
            c
            cs
            c_pbid
            (v !-> Some (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_SDiv ast1 ast2)); s_ls)
            s_stk
            s_gs
            s_syms
            s_pc
            c_mdl
          ).
          split.
          {
            apply Sym_Step_OP.
            simpl.
            rewrite <- H3.
            rewrite <- H4.
            reflexivity.
          }
          {
            apply OA_State.
            exists m.
            apply OAV_State; try assumption.
            apply store_update_correspondence.
            {
              rewrite <- H10.
              eapply OA_Some.
              { reflexivity. }
              {
                simpl.
                inversion H11; subst.
                inversion H17; subst.
                reflexivity.
              }
            }
            { assumption. }
          }
        }
        (* TODO: those are similar to the Sort_BV1 case *)
        { admit. }
        { admit. }
        { admit. }
        { admit. }
      }
      (* URem *)
      { admit. }
      (* SRem *)
      { admit. }
      (* Shl *)
      {
        simpl in H10.
        destruct
          (eval_exp c_ls c_gs (Some (TYPE_I w)) e1) as [dv1 | ] eqn:E1,
          (eval_exp c_ls c_gs (Some (TYPE_I w)) e2) as [dv2 | ] eqn:E2;
        try discriminate H10.
        destruct dv1 as [di1 | | ] , dv2 as [di2 | | ];
        try (
          unfold eval_ibinop in H10;
          destruct di1; discriminate H10
        );
        try (
          unfold eval_ibinop in H10;
          destruct di2; discriminate H10
        );
        try (
          unfold eval_ibinop in H10;
          discriminate H10
        );
        try (
          apply has_no_poison_eval_exp in E1; try assumption;
          destruct E1; reflexivity
        );
        try (
          apply has_no_poison_eval_exp in E2; try assumption;
          destruct E2; reflexivity
        ).
        unfold eval_ibinop in H10.
        destruct di1 as [n1 | n1 | n1 | n1 | n1], di2 as [n2 | n2 | n2 | n2 | n2];
        try (discriminate H10).
        {
          simpl in H10.
          destruct (Int1.unsigned n2 >=? 1)%Z eqn:En2.
          {
            inversion H10; subst.
            inversion H0; subst.
            inversion H11; subst.
            specialize (H2 v).
            rewrite update_map_eq in H2.
            destruct H2.
            reflexivity.
          }
          {
            assert(L1 :
              over_approx_via_model
                (eval_exp c_ls c_gs (Some (TYPE_I w)) e1)
                (sym_eval_exp s_ls s_gs (Some (TYPE_I w)) e1)
                m
            ).
            { apply eval_exp_correspondence; assumption. }
            assert(L2 :
              over_approx_via_model
                (eval_exp c_ls c_gs (Some (TYPE_I w)) e2)
                (sym_eval_exp s_ls s_gs (Some (TYPE_I w)) e2)
                m
            ).
            { apply eval_exp_correspondence; assumption. }
            rewrite E1 in L1.
            rewrite E2 in L2.
            inversion L1; subst.
            inversion L2; subst.
            rename sort into sort1, ast into ast1, sort0 into sort2, ast0 into ast2.
            assert(Lsort1 : sort1 = Sort_BV1).
            { eapply infer_sort. eassumption. }
            assert(Lsort2 : sort2 = Sort_BV1).
            { eapply infer_sort. eassumption. }
            subst.
            exists (mk_sym_state
              (next_inst_counter c_ic c)
              c
              cs
              c_pbid
              (v !-> Some (Expr Sort_BV1 (AST_BinOp Sort_BV1 SMT_Shl ast1 ast2)); s_ls)
              s_stk
              s_gs
              s_syms
              s_pc
              c_mdl
            ).
            split.
            {
              apply Sym_Step_OP.
              simpl.
              rewrite <- H3.
              rewrite <- H4.
              reflexivity.
            }
            {
              apply OA_State.
              exists m.
              apply OAV_State; try assumption.
              apply store_update_correspondence.
              {
                rewrite <- H10.
                eapply OA_Some.
                { reflexivity. }
                {
                  simpl.
                  inversion H11; subst.
                  assert(Ln2 : n2 = Int1.repr 0).
                  { apply int1_lt_one. assumption. }
                  inversion H17; subst.
                  rewrite H14.
                  rewrite Int1.shl_zero.
                  reflexivity.
                }
              }
              { assumption. }
            }
          }
        }
        (* TODO: should be similar *)
        { admit. }
        { admit. }
        { admit. }
        { admit. }
      }
    }
  }
  (* Phi *)
  {
    assert(L :
      over_approx_via_model
        (eval_phi_args c_ls c_gs t args pbid)
        (sym_eval_phi_args s_ls s_gs t args pbid)
        m
    ).
    {
      apply eval_phi_args_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H5; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H10 in *. discriminate H3. }
    {
      exists (mk_sym_state
        (next_inst_counter c_ic c)
        c
        cs
        (Some pbid)
        (v !-> Some (Expr sort ast); s_ls)
        s_stk
        s_gs
        s_syms
        s_pc
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Phi.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        apply store_update_correspondence.
        {
          rewrite H10 in H2.
          rewrite <- H2.
          eapply OA_Some; reflexivity.
        }
        { assumption. }
      }
    }
  }
  (* TERM_UnconditionalBr *)
  {
    exists (mk_sym_state
      (mk_inst_counter (ic_fid c_ic) (tbid) (get_cmd_id c))
      c
      cs
      (Some (ic_bid c_ic))
      s_ls
      s_stk
      s_gs
      s_syms
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_UnconditionalBr with (d := d) (b := b); assumption. }
    {
      apply OA_State.
      exists m.
      apply OAV_State; try assumption.
    }
  }
  { (* TERM_Br True *)
    assert(L :
      over_approx_via_model
        (eval_exp c_ls c_gs (Some (TYPE_I 1)) e)
        (sym_eval_exp s_ls s_gs (Some (TYPE_I 1)) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H5; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H10 in *. discriminate H3. }
    {
      rewrite H10 in H2.
      inversion H2; subst.
      apply infer_sort in H5.
      subst.  (* TODO: why rewrite does not work? *)
      exists (mk_sym_state
        (mk_inst_counter (ic_fid c_ic) (bid1) (get_cmd_id c))
        c
        cs
        (Some (ic_bid c_ic))
        s_ls
        s_stk
        s_gs
        s_syms
        (AST_BinOp Sort_BV1 SMT_And s_pc ast)
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Br_True with (d := d) (b := b); try assumption.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        simpl.
        inversion H2; subst.
        rewrite H28, H5.
        reflexivity.
      }
    }
  }
  (* TERM_Br False *)
  {
    assert(L :
      over_approx_via_model
        (eval_exp c_ls c_gs (Some (TYPE_I 1)) e)
        (sym_eval_exp s_ls s_gs (Some (TYPE_I 1)) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H5; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H10 in *. discriminate H3. }
    {
      rewrite H10 in H2.
      inversion H2; subst.
      apply infer_sort in H5.
      subst.
      exists (mk_sym_state
        (mk_inst_counter (ic_fid c_ic) (bid2) (get_cmd_id c))
        c
        cs
        (Some (ic_bid c_ic))
        s_ls
        s_stk
        s_gs
        s_syms
        (AST_BinOp Sort_BV1 SMT_And s_pc (AST_Not Sort_BV1 ast))
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Br_False with (d := d) (b := b); try assumption.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        simpl.
        inversion H2; subst.
        rewrite H28, H5.
        reflexivity.
      }
    }
  }
  (* INSTR_VoidCall *)
  {
    rename ls' into c_ls'.
    assert(L :
      exists s_ls',
        create_local_smt_store d s_ls s_gs args = Some s_ls' /\
        over_approx_store_via s_ls' c_ls' m
    ).
    {
      apply create_local_store_correspondence with (c_ls := c_ls) (c_gs := c_gs); try assumption.
      inversion Hiss; subst.
      inversion H5; subst.
      assumption.
    }
    destruct L as [s_ls' [L_1 L_2]].
    exists (mk_sym_state
      (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'0))
      c'0
      cs'
      None
      s_ls'
      ((Sym_Frame s_ls (next_inst_counter c_ic c) c_pbid None) :: s_stk)
      s_gs
      s_syms
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_VoidCall; assumption. }
    {
      apply OA_State.
      exists m.
      apply OAV_State; try assumption.
      apply OA_Stack_NonEmpty; try assumption.
      apply OA_Frame .
      assumption.
    }
  }
  (* INSTR_Call *)
  {
    rename ls' into c_ls'.
    assert(L :
      exists s_ls',
        create_local_smt_store d s_ls s_gs args = Some s_ls' /\
        over_approx_store_via s_ls' c_ls' m
    ).
    {
      apply create_local_store_correspondence with (c_ls := c_ls) (c_gs := c_gs); try assumption.
      inversion Hiss; subst.
      inversion H5; subst.
      assumption.
    }
    destruct L as [s_ls' [L_1 L_2]].
    exists (mk_sym_state
      (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'0))
      c'0
      cs'
      None
      s_ls'
      ((Sym_Frame s_ls (next_inst_counter c_ic c) c_pbid (Some v)) :: s_stk)
      s_gs
      s_syms
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_Call; assumption. }
    {
      apply OA_State.
      exists m.
      apply OAV_State; try assumption.
      apply OA_Stack_NonEmpty; try assumption.
      apply OA_Frame.
      assumption.
    }
  }
  (* TERM_RetVoid *)
  {
    inversion H24; subst.
    inversion H5; subst.
    exists (mk_sym_state
      ic'
      c'0
      cs'
      pbid'
      s_s
      s_stk0
      s_gs
      s_syms
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_RetVoid with (d := d); assumption. }
    {
      apply OA_State.
      exists m.
      apply OAV_State; assumption.
    }
  }
  (* TERM_Ret *)
  {
    inversion H25; subst.
    inversion H5; subst.
    assert(L :
      over_approx_via_model
        (eval_exp c_ls c_gs (Some t) e)
        (sym_eval_exp s_ls s_gs (Some t) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H6; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H10 in *. discriminate H3. }
    {
      exists (mk_sym_state
        ic'
        c'0
        cs'
        pbid'
        (v !-> Some (Expr sort ast); s_s)
        s_stk0
        s_gs
        s_syms
        s_pc
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Ret with (d := d); try assumption.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        apply store_update_correspondence.
        {
          rewrite H10 in H2.
          rewrite <- H2.
          eapply OA_Some; reflexivity.
        }
        { assumption. }
      }
    }
  }
  {
    inversion Hws; subst.
    exists (mk_sym_state
      (next_inst_counter c_ic c)
      c
      cs
      c_pbid
      (v !-> Some (Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name s_syms))); s_ls)
      s_stk
      s_gs
      (extend_names s_syms)
      s_pc
      c_mdl
    ).
    split.
    { apply Sym_Step_MakeSymbolicInt32 with (d := d); assumption. }
    {
      apply OA_State.
      exists (
        mk_smt_model
          (StringMap.update_map (bv_model m) (fresh_name s_syms) n)
      ).
      apply OAV_State.
      {
        apply store_update_correspondence.
        {
          replace (DI_I32 (repr n)) with (make_dynamic_int Sort_BV32 (Int32.repr n)).
          {
            eapply OA_Some; try reflexivity.
            simpl.
            rewrite StringMap.update_map_eq.
            reflexivity.
          }
          { reflexivity. }
        }
        {
          apply over_approx_store_non_interference with (syms := s_syms); try assumption.
          apply fresh_name_lemma.
        }
      }
      {
        apply over_approx_stack_non_interference with (syms := s_syms); try assumption.
        apply fresh_name_lemma.
      }
      {
        apply over_approx_store_non_interference with (syms := s_syms); try assumption.
        apply fresh_name_lemma.
      }
      {
        rewrite <- H27.
        symmetry.
        apply subexpr_non_interference.
        inversion H18; subst.
        specialize (H2 (fresh_name s_syms)).
        intros Hse.
        apply H2 in Hse.
        apply fresh_name_lemma in Hse.
        assumption.
      }
    }
  }
  {
    assert(L :
      over_approx_via_model
        (eval_exp c_ls c_gs (Some (TYPE_I 1)) e)
        (sym_eval_exp s_ls s_gs (Some (TYPE_I 1)) e)
        m
    ).
    {
      apply eval_exp_correspondence; try assumption.
      inversion Hiss; subst.
      inversion H5; subst.
      specialize (H3 (TYPE_I 1, e, attrs)).
      assert(Larg : is_supported_function_arg (TYPE_I 1, e, attrs)).
      { apply H3. apply in_eq. }
      inversion Larg; subst.
      assumption.
    }
    inversion L; subst.
    { rewrite H13 in *. discriminate H3. }
    {
      rewrite H13 in H2.
      inversion H2; subst.
      apply infer_sort in H5.
      subst.
      exists (mk_sym_state
        (next_inst_counter c_ic c)
        c
        cs
        c_pbid
        s_ls
        s_stk
        s_gs
        s_syms
        (AST_BinOp Sort_BV1 SMT_And s_pc ast)
        c_mdl
      ).
      split.
      {
        apply Sym_Step_Assume with (d := d); try assumption.
        symmetry.
        assumption.
      }
      {
        apply OA_State.
        exists m.
        apply OAV_State; try assumption.
        simpl.
        inversion H2; subst.
        rewrite H28, H5.
        reflexivity.
      }
    }
  }
Admitted.

(* TODO: can we prove without additional assumptions? *)
Lemma error_correspondence: forall c s,
  is_supported_state c ->
  error_state c ->
  over_approx s c ->
  error_sym_state s.
Proof.
  intros c s His He Hoa.
  inversion Hoa.
  destruct H as [m H].
  inversion H; subst.
  inversion He; subst.
  { apply ESS_Assert with (d := d); assumption. }
  { apply ESS_Unreachable. }
  {
    inversion His; subst.
    inversion H8; subst.
    {
      inversion H7; subst; (
        inversion H1; subst;
        inversion H15
      ).
    }
    {
      assert(L :
        over_approx_via_model
          (eval_exp c_ls c_gs (Some (TYPE_I w)) e2)
          (sym_eval_exp s_ls s_gs (Some (TYPE_I w)) e2)
          m
      ).
      { apply eval_exp_correspondence; assumption. }
      inversion L; subst.
      { rewrite H13 in H1. discriminate. }
      {
        apply ESS_DivisionByZero with (se := (Expr sort ast)).
        { assumption. }
        { symmetry. assumption. }
        {
          rewrite H13 in H0.
          inversion H0; subst.
          unfold sat, sym_division_error_condition.
          exists m.
          unfold sat_via.
          destruct sort; (
            simpl;
            rewrite H5;
            unfold smt_eval_cmpop_by_sort, smt_eval_cmpop_generic;
            simpl;
            simpl in H14;
            rewrite H14;
            reflexivity
          ).
        }
      }
    }
  }
  {
    inversion His; subst.
    inversion H8; subst.
    inversion H1; subst.
    { inversion H14. }
    {
      assert(L :
        over_approx_via_model
          (eval_exp c_ls c_gs (Some (TYPE_I w)) e2)
          (sym_eval_exp s_ls s_gs (Some (TYPE_I w)) e2)
          m
      ).
      { apply eval_exp_correspondence; assumption. }
      inversion L; subst.
      { rewrite H6 in H1. discriminate. }
      {
        apply ESS_Shl with (se := (Expr sort ast)).
        { symmetry. assumption. }
        {
          rewrite H6 in H0.
          inversion H0; subst.
          unfold sat, sym_shl_error_condition.
          exists m.
          unfold sat_via.
          destruct sort; (
            simpl;
            simpl in H13;
            rewrite H5;
            unfold smt_eval_cmpop_by_sort, smt_eval_cmpop_generic;
            simpl;
            rewrite H13;
            reflexivity
          ).
        }
      }
    }
  }
Qed.

Lemma init_state_correspondence : forall mdl fid,
  (exists c, (init_state mdl fid) = Some c) <-> (exists s, (init_sym_state mdl fid) = Some s).
Proof.
  intros mdl fid.
  split; intros H.
  {
    destruct H as [c H].
    unfold init_state in H.
    destruct (find_function mdl fid) as [c_d | ] eqn:Ec_d; try discriminate H.
    destruct (build_inst_counter mdl c_d) as [c_ic | ] eqn:Ec_ic; try discriminate H.
    destruct (entry_block c_d) as [c_b | ] eqn:Ec_b; try discriminate H.
    destruct (blk_cmds c_b) as [ | c_cmd c_cmds ] eqn:Ec_cs; try discriminate H.
    exists (mk_sym_state
      c_ic
      c_cmd
      c_cmds
      None
      (init_local_smt_store mdl c_d)
      []
      (init_global_smt_store mdl)
      []
      smt_ast_true
      mdl
    ).
    unfold init_sym_state.
    simpl.
    rewrite Ec_d, Ec_ic, Ec_b, Ec_cs.
    reflexivity.
  }
  {
    destruct H as [s H].
    unfold init_sym_state in H.
    destruct (find_function mdl fid) as [s_d | ] eqn:Es_d; try discriminate H.
    destruct (build_inst_counter mdl s_d) as [s_ic | ] eqn:Es_ic; try discriminate H.
    destruct (entry_block s_d) as [s_b | ] eqn:Es_b; try discriminate H.
    destruct (blk_cmds s_b) as [ | s_cmd s_cmds ] eqn:Es_cs; try discriminate H.
    exists (mk_state
      s_ic
      s_cmd
      s_cmds
      None
      (init_local_store mdl s_d)
      []
      (init_global_store mdl)
      mdl
    ).
    unfold init_state.
    simpl.
    rewrite Es_d, Es_ic, Es_b, Es_cs.
    reflexivity.
  }
Qed.

Lemma over_approx_init_states : forall mdl fid s c,
  init_sym_state mdl fid = Some s ->
  init_state mdl fid = Some c ->
  over_approx s c.
Proof.
  intros mdl fid s c Hs Hc.
  unfold init_sym_state in Hs.
  destruct (find_function mdl fid) as [s_d | ] eqn:Es_d; try discriminate Hs.
  destruct (build_inst_counter mdl s_d) as [s_ic | ] eqn:Es_ic; try discriminate Hs.
  destruct (entry_block s_d) as [s_b | ] eqn:Es_b; try discriminate Hs.
  destruct (blk_cmds s_b) as [ | s_cmd s_cmds ] eqn:Es_cs; try discriminate Hs.
  unfold init_state in Hc.
  destruct (find_function mdl fid) as [c_d | ] eqn:Ec_d; try discriminate Hc.
  destruct (build_inst_counter mdl c_d) as [c_ic | ] eqn:Ec_ic; try discriminate Hc.
  destruct (entry_block c_d) as [c_b | ] eqn:Ec_b; try discriminate Hc.
  destruct (blk_cmds c_b) as [ | c_cmd c_cmds ] eqn:Ec_cs; try discriminate Hc.
  inversion Es_d; subst.
  rewrite Ec_ic in Es_ic.
  inversion Es_ic; subst.
  rewrite Ec_b in Es_b.
  inversion Es_b; subst.
  rewrite Ec_cs in Es_cs.
  inversion Es_cs; subst.
  apply OA_State.
  exists default_model.
  inversion Hs; subst.
  inversion Hc; subst.
  apply OAV_State.
  {
    unfold init_local_smt_store, init_local_store.
    apply empty_store_correspondence.
  }
  { apply OA_Stack_Empty. }
  {
    unfold init_global_smt_store, init_global_store.
    apply empty_store_correspondence.
  }
  { reflexivity. }
Qed.

Lemma completeness :
  forall (mdl : llvm_module) (fid : function_id) (init_c c : state),
    is_supported_module mdl ->
    (init_state mdl fid) = Some init_c ->
    multi_ns_step init_c c ->
    (exists init_s s,
      (init_sym_state mdl fid) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c).
Proof.
  intros mdl fid init_c c Hism Hinit Hms.
  (* TODO: rename *)
  assert(L1 : exists init_s, init_sym_state mdl fid = Some init_s).
  { apply (init_state_correspondence mdl fid). exists init_c. assumption. }
  destruct L1 as [init_s L1].
  exists init_s.
  induction Hms as [init_c c | init_c c c'].
  {
    (* TODO: rename *)
    assert(L2 : exists s, sym_step init_s s /\ over_approx s c).
    {
      apply completeness_single_step with (c := init_c).
      { apply (is_supported_init_state mdl fid); assumption. }
      { apply (has_no_poison_init_state mdl fid). assumption. }
      { assumption. }
      { apply (well_scoped_init_sym_state mdl fid). assumption. }
      { apply (over_approx_init_states mdl fid); assumption. }
    }
    destruct L2 as [s [L2_1 L2_2]].
    exists s.
    split.
    { assumption. }
    {
      split.
      { apply multi_base. assumption. }
      { assumption. }
    }
  }
  {
    (* TODO: rename *)
    assert(L3 :
      exists s,
        init_sym_state mdl fid = Some init_s /\ multi_sym_step init_s s /\ over_approx s c
    ).
    { apply IHHms. assumption. }
    destruct L3 as [s [L3_1 [L3_2 L3_3]]].
    (* TODO: rename *)
    assert(L4 : exists s', sym_step s s' /\ over_approx s' c').
    {
      apply completeness_single_step with (c := c).
      {
        apply (is_supported_multi_step init_c).
        { apply multi_ns_step_soundness. assumption. }
        { apply (is_supported_init_state mdl fid); assumption. }
      }
      { apply has_no_poison_multi_ns_step with (s1 := init_c). assumption. }
      { assumption. }
      {
        apply well_scoped_multi_sym_step with (s := init_s).
        apply (well_scoped_init_sym_state mdl fid).
        { assumption. }
        { assumption. }
      }
      { assumption. }
    }
    destruct L4 as [s' [L4_1 L4_2]].
    exists s'.
    split.
    { assumption. }
    {
      split.
      { apply multi_trans with (y := s); assumption. }
      { assumption. }
    }
  }
Qed.
