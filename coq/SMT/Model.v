From Coq Require Import Logic.Eqdep.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE Require Import DynamicValue.

From SE.Numeric Require Import Integers.

From SE.SMT Require Import Expr.

From SE.Utils Require Import StringMap.

(* TODO: use equiv_smt_expr_property to shorten proofs *)

Inductive symbol : Type :=
  | Symbol_BV (s : string)
.

Record smt_model := mk_smt_model {
  bv_model : total_map Z;
}.

Definition default_model := mk_smt_model (empty_map 0%Z).

Definition repr_by_sort (s : smt_sort) (n : Z) : (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1
  | Sort_BV8
  | Sort_BV16
  | Sort_BV24
  | Sort_BV32
  | Sort_BV48
  | Sort_BV56
  | Sort_BV64 => repr n
  end
.

Definition smt_eval_binop_generic {Int} `{VInt Int} (op : smt_binop) (x y : Int) : Int :=
  match op with
  | SMT_Add => (add x y)
  | SMT_Sub => (sub x y)
  | SMT_Mul => (mul x y)
  | SMT_UDiv => (divu x y)
  | SMT_SDiv => (divs x y)
  | SMT_URem => (modu x y)
  | SMT_SRem => (mods x y)
  | SMT_And => (and x y)
  | SMT_Or => (or x y)
  | SMT_Xor => (xor x y)
  | SMT_Shl => (shl x y)
  | SMT_LShr => (shru x y)
  | SMT_AShr => (shr x y)
  end
.

Definition binop_predicate (s : smt_sort) :=
  smt_binop -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s)
.

Definition smt_eval_binop_by_sort op s (x y : (smt_sort_to_int_type s)) : (smt_sort_to_int_type s) :=
  let f :=
    match s return (binop_predicate s) with
    | Sort_BV1
    | Sort_BV8
    | Sort_BV16
    | Sort_BV24
    | Sort_BV32
    | Sort_BV48
    | Sort_BV56
    | Sort_BV64 => smt_eval_binop_generic
    end in
  f op x y
.

Definition smt_cmpop_to_comparison (op : smt_cmpop) : comparison :=
  match op with
  | SMT_Eq => Ceq
  | SMT_Ne => Cne
  | SMT_Ugt => Cgt
  | SMT_Uge => Cge
  | SMT_Ult => Clt
  | SMT_Ule => Cle
  | SMT_Sgt => Cgt
  | SMT_Sge => Cge
  | SMT_Slt => Clt
  | SMT_Sle => Cle
  end
.

Definition smt_eval_cmpop_generic {Int} `{VInt Int} (op : smt_cmpop) (x y : Int) : bool :=
  match op with
  | SMT_Ugt
  | SMT_Uge
  | SMT_Ult
  | SMT_Ule =>
    cmpu (smt_cmpop_to_comparison op) x y
  |_ =>
    cmp (smt_cmpop_to_comparison op) x y
  end
.

Definition cmpop_predicate (s : smt_sort) :=
  smt_cmpop -> (smt_sort_to_int_type s) -> (smt_sort_to_int_type s) -> bool
.

Definition smt_eval_cmpop_by_sort op s (x y : (smt_sort_to_int_type s)) : int1 :=
  let f :=
    match s return (cmpop_predicate s) with
    | Sort_BV1
    | Sort_BV8
    | Sort_BV16
    | Sort_BV24
    | Sort_BV32
    | Sort_BV48
    | Sort_BV56
    | Sort_BV64 => smt_eval_cmpop_generic
    end in
  if (f op x y) then one else zero
.

Definition create_mone_by_sort (s : smt_sort) : (smt_sort_to_int_type s) :=
  match s with
  | Sort_BV1 => Int1.mone
  | Sort_BV8 => Int8.mone
  | Sort_BV16 => Int16.mone
  | Sort_BV24 => Int24.mone
  | Sort_BV32 => Int32.mone
  | Sort_BV48 => Int48.mone
  | Sort_BV56 => Int56.mone
  | Sort_BV64 => Int64.mone
  end
.

Definition smt_eval_not_by_sort s (x : (smt_sort_to_int_type s)) : (smt_sort_to_int_type s) :=
  smt_eval_binop_by_sort SMT_Xor s x (create_mone_by_sort s)
.

Definition convert_predicate (s : smt_sort) :=
  (smt_sort_to_int_type s) -> Z
.

Definition unsigned_by_sort s (x : (smt_sort_to_int_type s)) : Z :=
  let f :=
    match s return (convert_predicate s) with
    | Sort_BV1
    | Sort_BV8
    | Sort_BV16
    | Sort_BV24
    | Sort_BV32
    | Sort_BV48
    | Sort_BV56
    | Sort_BV64 => unsigned
    end in
  f x
.

Definition smt_eval_zext_by_sort s (x : (smt_sort_to_int_type s)) cast_sort : (smt_sort_to_int_type cast_sort) :=
  match cast_sort with
  | Sort_BV1 => (Int1.repr (unsigned_by_sort s x))
  | Sort_BV8 => (Int8.repr (unsigned_by_sort s x))
  | Sort_BV16 => (Int16.repr (unsigned_by_sort s x))
  | Sort_BV24 => (Int24.repr (unsigned_by_sort s x))
  | Sort_BV32 => (Int32.repr (unsigned_by_sort s x))
  | Sort_BV48 => (Int48.repr (unsigned_by_sort s x))
  | Sort_BV56 => (Int56.repr (unsigned_by_sort s x))
  | Sort_BV64 => (Int64.repr (unsigned_by_sort s x))
  end
.

Definition signed_by_sort s (x : (smt_sort_to_int_type s)) : Z :=
  let f :=
    match s return (convert_predicate s) with
    | Sort_BV1
    | Sort_BV8
    | Sort_BV16
    | Sort_BV24
    | Sort_BV32
    | Sort_BV48
    | Sort_BV56
    | Sort_BV64 => signed
    end in
  f x
.

Definition smt_eval_sext_by_sort s (x : (smt_sort_to_int_type s)) cast_sort : (smt_sort_to_int_type cast_sort) :=
  match cast_sort with
  | Sort_BV1 => (Int1.repr (signed_by_sort s x))
  | Sort_BV8 => (Int8.repr (signed_by_sort s x))
  | Sort_BV16 => (Int16.repr (signed_by_sort s x))
  | Sort_BV24 => (Int24.repr (signed_by_sort s x))
  | Sort_BV32 => (Int32.repr (signed_by_sort s x))
  | Sort_BV48 => (Int48.repr (signed_by_sort s x))
  | Sort_BV56 => (Int56.repr (signed_by_sort s x))
  | Sort_BV64 => (Int64.repr (signed_by_sort s x))
  end
.

Definition smt_eval_extract_by_sort s (x : (smt_sort_to_int_type s)) cast_sort : (smt_sort_to_int_type cast_sort) :=
  match cast_sort with
  | Sort_BV1 => Int1.repr (unsigned (Int1.repr (unsigned_by_sort s x)))
  | Sort_BV8 => Int8.repr (unsigned (Int8.repr (unsigned_by_sort s x)))
  | Sort_BV16 => Int16.repr (unsigned (Int16.repr (unsigned_by_sort s x)))
  | Sort_BV24 => Int24.repr (unsigned (Int24.repr (unsigned_by_sort s x)))
  | Sort_BV32 => Int32.repr (unsigned (Int32.repr (unsigned_by_sort s x)))
  | Sort_BV48 => Int48.repr (unsigned (Int48.repr (unsigned_by_sort s x)))
  | Sort_BV56 => Int56.repr (unsigned (Int56.repr (unsigned_by_sort s x)))
  | Sort_BV64 => Int64.repr (unsigned (Int64.repr (unsigned_by_sort s x)))
  end
.

Definition smt_eval_ite s (cond : int1) (x y : (smt_sort_to_int_type s)) :=
  if eq cond one then x else y
.

Fixpoint smt_eval_ast (m : smt_model) (s : smt_sort) (ast : smt_ast s) : (smt_sort_to_int_type s) :=
  match ast with
  | AST_Const arg_sort n => n
  | AST_Var arg_sort x => repr_by_sort arg_sort ((bv_model m) x)
  | AST_BinOp arg_sort op ast1 ast2 =>
      smt_eval_binop_by_sort
        op
        arg_sort
        (smt_eval_ast m arg_sort ast1)
        (smt_eval_ast m arg_sort ast2)
  | AST_CmpOp arg_sort op ast1 ast2 =>
      smt_eval_cmpop_by_sort
        op
        arg_sort
        (smt_eval_ast m arg_sort ast1)
        (smt_eval_ast m arg_sort ast2)
  | AST_Not arg_sort ast =>
      smt_eval_not_by_sort arg_sort (smt_eval_ast m arg_sort ast)
  | AST_ZExt arg_sort ast cast_sort =>
      smt_eval_zext_by_sort arg_sort (smt_eval_ast m arg_sort ast) cast_sort
  | AST_SExt arg_sort ast cast_sort =>
      smt_eval_sext_by_sort arg_sort (smt_eval_ast m arg_sort ast) cast_sort
  | AST_Extract arg_sort ast cast_sort =>
      smt_eval_extract_by_sort arg_sort (smt_eval_ast m arg_sort ast) cast_sort
  | AST_ITE arg_sort cond e1 e2 =>
      smt_eval_ite
        arg_sort
        (smt_eval_ast m Sort_BV1 cond)
        (smt_eval_ast m arg_sort e1)
        (smt_eval_ast m arg_sort e2)
  end
.

Definition smt_eval (m : smt_model) (e : smt_expr) : (smt_sort_to_int_type (get_sort e)) :=
  match e with
  | Expr sort ast => smt_eval_ast m sort ast
  end
.

Definition sat_via (ast : smt_ast_bool) (m : smt_model) :=
  smt_eval_ast m Sort_BV1 ast = one
.

Definition sat (ast : smt_ast_bool) :=
  exists (m : smt_model), sat_via ast m
.

Lemma sat_and : forall (e1 e2 : smt_ast_bool) (m : smt_model),
  sat_via (AST_BinOp Sort_BV1 SMT_And e1 e2) m ->
  (sat_via e1 m /\ sat_via e2 m).
Proof.
 intros e1 e2 m Hsat.
 unfold sat_via in Hsat.
 simpl in Hsat.
 split.
 {
   apply int1_and_one_infer_left in Hsat.
   assumption.
 }
 {
   apply int1_and_one_infer_right in Hsat.
   assumption.
 }
Qed.

Lemma sat_and_intro : forall (e1 e2 : smt_ast_bool) (m : smt_model),
  sat_via e1 m ->
  sat_via e2 m ->
  sat_via (AST_BinOp Sort_BV1 SMT_And e1 e2) m.
Proof.
 intros e1 e2 m Hsat1 Hsat2.
 unfold sat_via in *.
 simpl.
 rewrite Hsat1, Hsat2.
 reflexivity.
Qed.

Lemma sat_intro_and : forall (ast1 ast2 : smt_ast_bool) (m : smt_model),
  sat_via ast1 m ->
  sat_via ast2 m ->
  sat_via (AST_BinOp Sort_BV1 SMT_And ast1 ast2) m.
Proof.
  intros ast1 ast2 m Hsat1 Hsat2.
  unfold sat_via in *.
  simpl.
  rewrite Hsat1, Hsat2.
  reflexivity.
Qed.

Lemma sat_and_left : forall (ast1 ast2 : smt_ast_bool) (m : smt_model),
  sat_via (AST_BinOp Sort_BV1 SMT_And ast1 ast2) m ->
  sat_via ast1 m.
Proof.
  intros ast1 ast2 m Hsat.
  unfold sat_via in *.
  simpl in Hsat.
  apply int1_and_one_infer_left in Hsat.
  assumption.
Qed.

Lemma sat_and_right : forall (ast1 ast2 : smt_ast_bool) (m : smt_model),
  sat_via (AST_BinOp Sort_BV1 SMT_And ast1 ast2) m ->
  sat_via ast2 m.
Proof.
  intros ast1 ast2 m Hsat.
  unfold sat_via in *.
  simpl in Hsat.
  apply int1_and_one_infer_right in Hsat.
  assumption.
Qed.

Lemma sat_intro_or_left : forall (ast1 ast2 : smt_ast_bool) (m : smt_model),
  sat_via ast1 m ->
  sat_via (AST_BinOp Sort_BV1 SMT_Or ast1 ast2) m.
Proof.
  intros ast1 ast2 m Hsat.
  unfold sat_via in *.
  simpl.
  rewrite Hsat.
  apply int1_or_one_left.
Qed.

Lemma sat_intro_or_right : forall (ast1 ast2 : smt_ast_bool) (m : smt_model),
  sat_via ast2 m ->
  sat_via (AST_BinOp Sort_BV1 SMT_Or ast1 ast2) m.
Proof.
  intros ast1 ast2 m Hsat.
  unfold sat_via in *.
  simpl.
  rewrite Hsat.
  apply int1_or_one_right.
Qed.

Definition unsat (ast : smt_ast_bool) := ~ sat ast.

Lemma unsat_false :
  unsat smt_ast_false.
Proof.
  unfold unsat.
  intros Hsat.
  unfold sat, sat_via in Hsat.
  simpl in Hsat.
  assert(Int1.zero = Int1.one).
  { destruct Hsat as [m Hsat]. assumption. }
  discriminate.
Qed.

Lemma unsat_and_left : forall (e1 e2 : smt_ast_bool),
  unsat e1 ->
  unsat (AST_BinOp Sort_BV1 SMT_And e1 e2).
Proof.
  intros e1 e2 Hunsat.
  unfold unsat in *.
  intros Hsat.
  apply Hunsat.
  unfold sat in *.
  destruct Hsat as [m Hsat].
  exists m.
  unfold sat_via in *.
  simpl in Hsat.
  apply int1_and_one_infer_left in Hsat.
  assumption.
Qed.

Lemma unsat_and_right : forall (e1 e2 : smt_ast_bool),
  unsat e2 ->
  unsat (AST_BinOp Sort_BV1 SMT_And e1 e2).
Proof.
  intros e1 e2 Hunsat.
  unfold unsat in *.
  intros Hsat.
  apply Hunsat.
  unfold sat in *.
  destruct Hsat as [m Hsat].
  exists m.
  unfold sat_via in *.
  simpl in Hsat.
  apply int1_and_one_infer_right in Hsat.
  assumption.
Qed.

Lemma subexpr_non_interference : forall sort (ast : smt_ast sort) x m n,
  (~ contains_var (Expr sort ast) x ) ->
  smt_eval_ast m sort ast = smt_eval_ast (mk_smt_model (x !-> n; bv_model m)) sort ast.
Proof.
  intros sort ast x m n H.
  induction ast; simpl.
  { reflexivity. }
  {
    destruct (x =? x0)%string eqn:E.
    {
      rewrite String.eqb_eq in E.
      rewrite E in H.
      destruct H.
      apply ContainsVar with (sort := s).
      apply SubExpr_Refl.
    }
    {
      rewrite String.eqb_neq in E.
      rewrite update_map_neq; try assumption.
      reflexivity.
    }
  }
  {
    assert(L1 : ~ contains_var (Expr s ast1) x).
    { intros Hse. apply H. apply contains_var_binop_intro_l. assumption. }
    assert(L2 : ~ contains_var (Expr s ast2) x).
    { intros Hse. apply H. apply contains_var_binop_intro_r. assumption. }
    apply IHast1 in L1.
    apply IHast2 in L2.
    rewrite L1, L2.
    reflexivity.
  }
  {
    assert(L1 : ~ contains_var (Expr s ast1) x).
    { intros Hse. apply H. apply contains_var_cmpop_intro_l. assumption. }
    assert(L2 : ~ contains_var (Expr s ast2) x).
    { intros Hse. apply H. apply contains_var_cmpop_intro_r. assumption. }
    apply IHast1 in L1.
    apply IHast2 in L2.
    rewrite L1, L2.
    reflexivity.
  }
  {
    assert(L : ~ contains_var (Expr s ast) x).
    { intros Hse. apply H. apply contains_var_not_intro. assumption. }
    apply IHast in L.
    rewrite L.
    reflexivity.
  }
  {
    assert(L : ~ contains_var (Expr s ast) x).
    { intros Hse. apply H. apply contains_var_zext_intro. assumption. }
    apply IHast in L.
    rewrite L.
    reflexivity.
  }
  {
    assert(L : ~ contains_var (Expr s ast) x).
    { intros Hse. apply H. apply contains_var_sext_intro. assumption. }
    apply IHast in L.
    rewrite L.
    reflexivity.
  }
  {
    assert(L : ~ contains_var (Expr s ast) x).
    { intros Hse. apply H. apply contains_var_extract_intro. assumption. }
    apply IHast in L.
    rewrite L.
    reflexivity.
  }
  {
    assert(L1 : ~ contains_var (Expr Sort_BV1 ast1) x).
    { intros Hse. apply H. apply contains_var_ite_intro_cond. assumption. }
    assert(L2 : ~ contains_var (Expr s ast2) x).
    { intros Hse. apply H. apply contains_var_ite_intro_l. assumption. }
    assert(L3 : ~ contains_var (Expr s ast3) x).
    { intros Hse. apply H. apply contains_var_ite_intro_r. assumption. }
    apply IHast1 in L1.
    apply IHast2 in L2.
    apply IHast3 in L3.
    rewrite L1, L2, L3.
    reflexivity.
  }
Qed.

Inductive equiv_smt_expr : smt_expr -> smt_expr -> Prop :=
  | EquivExpr : forall s (ast1 ast2 : smt_ast s),
      (forall m, smt_eval_ast m s ast1 = smt_eval_ast m s ast2) ->
      equiv_smt_expr (Expr s ast1) (Expr s ast2)
.

Lemma equiv_smt_expr_property : forall s (ast1 ast2 :smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s ast2) ->
  (forall m, smt_eval_ast m s ast1 = smt_eval_ast m s ast2).
Proof.
  intros s ast1 ast2 Heq.
  inversion Heq; subst.
  intros m.
  apply inj_pair2 in H1.
  apply inj_pair2 in H2.
  subst.
  apply H0.
Qed.

Lemma sort_injection : forall sort1 sort2 ast1 ast2,
  equiv_smt_expr (Expr sort1 ast1) (Expr sort2 ast2) ->
  sort1 = sort2.
Proof.
  intros sort1 sort2 ast1 ast2 H.
  inversion H; subst.
  reflexivity.
Qed.

Lemma equiv_smt_expr_refl : forall e, equiv_smt_expr e e.
Proof.
  intros e.
  destruct e as [sort ast].
  apply EquivExpr.
  intros m.
  reflexivity.
Qed.

Lemma equiv_smt_expr_symmetry : forall e1 e2,
  equiv_smt_expr e1 e2 -> equiv_smt_expr e2 e1.
Proof.
  intros e1 e2 H.
  inversion H; subst.
  apply EquivExpr.
  intros m.
  symmetry.
  apply H0.
Qed.

Lemma equiv_smt_expr_transitivity : forall e1 e2 e3,
  equiv_smt_expr e1 e2 -> equiv_smt_expr e2 e3 -> equiv_smt_expr e1 e3.
Proof.
  intros e1 e2 e3 H1 H2.
  inversion H1; subst.
  inversion H2; subst.
  apply inj_pair2 in H4.
  subst.
  rename ast4 into ast3.
  apply EquivExpr.
  intros m.
  specialize (H m).
  specialize (H5 m).
  rewrite H.
  assumption.
Qed.

Lemma equiv_smt_expr_sat_via : forall (ast1 ast2 : smt_ast_bool) (m : smt_model),
  equiv_smt_expr (Expr Sort_BV1 ast1) (Expr Sort_BV1 ast2) ->
  sat_via ast1 m ->
  sat_via ast2 m.
Proof.
  intros ast1 ast2 m Heq Hsat.
  unfold sat_via in *.
  inversion Heq; subst.
  apply inj_pair2 in H1, H2; subst.
  specialize (H0 m).
  rewrite Hsat in *.
  symmetry in H0.
  assumption.
Qed.

Lemma equiv_smt_expr_sat : forall (ast1 ast2 : smt_ast_bool),
  equiv_smt_expr (Expr Sort_BV1 ast1) (Expr Sort_BV1 ast2) ->
  sat ast1 ->
  sat ast2.
Proof.
  intros ast1 ast2 Heq Hsat.
  unfold sat in *.
  destruct Hsat as [m Hsat].
  exists m.
  eapply equiv_smt_expr_sat_via; eassumption.
Qed.

Lemma equiv_smt_expr_unsat : forall (ast1 ast2 : smt_ast_bool),
  equiv_smt_expr (Expr Sort_BV1 ast1) (Expr Sort_BV1 ast2) ->
  unsat ast1 ->
  unsat ast2.
Proof.
  intros ast1 ast2 Heq Hunsat.
  unfold unsat, sat in *.
  intros Hsat.
  apply Hunsat.
  destruct Hsat as [m Hsat].
  exists m.
  unfold sat_via in *.
  rewrite <- Hsat.
  inversion Heq; subst.
  apply inj_pair2 in H1, H2.
  subst.
  apply H0.
Qed.

Lemma equiv_smt_expr_binop : forall s op (ast1 ast2 ast3 ast4 : smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s ast2) ->
  equiv_smt_expr (Expr s ast3) (Expr s ast4) ->
  equiv_smt_expr
    (Expr s (AST_BinOp s op ast1 ast3))
    (Expr s (AST_BinOp s op ast2 ast4)).
Proof.
  intros s op ast1 ast2 ast3 ast4 H1 H2.
  apply EquivExpr.
  intros m.
  simpl.
  inversion H1; subst.
  apply inj_pair2 in H3, H4.
  subst.
  inversion H2; subst.
  apply inj_pair2 in H4, H5.
  subst.
  specialize (H0 m).
  specialize (H3 m).
  rewrite H0, H3.
  reflexivity.
Qed.

Lemma equiv_smt_expr_cmpop : forall s op (ast1 ast2 ast3 ast4 : smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s ast2) ->
  equiv_smt_expr (Expr s ast3) (Expr s ast4) ->
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s op ast1 ast3))
    (Expr Sort_BV1 (AST_CmpOp s op ast2 ast4)).
Proof.
  intros s op ast1 ast2 ast3 ast4 H1 H2.
  apply EquivExpr.
  intros m.
  simpl.
  inversion H1; subst.
  apply inj_pair2 in H3, H4.
  subst.
  inversion H2; subst.
  apply inj_pair2 in H4, H5.
  subst.
  specialize (H0 m).
  specialize (H3 m).
  rewrite H0, H3.
  reflexivity.
Qed.

Lemma equiv_smt_expr_not : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr (Expr s ast1) (Expr s ast2) ->
  equiv_smt_expr (Expr s (AST_Not s ast1)) (Expr s (AST_Not s ast2)).
Proof.
  intros s ast1 ast2 H.
  apply EquivExpr.
  intros m.
  simpl.
  inversion H; subst.
  apply inj_pair2 in H2, H3.
  subst.
  specialize (H1 m).
  rewrite H1.
  reflexivity.
Qed.

Lemma equiv_smt_expr_zext : forall s (ast1 ast2 : smt_ast s) cast_sort,
  equiv_smt_expr (Expr s ast1) (Expr s ast2) ->
  equiv_smt_expr
    (Expr cast_sort (AST_ZExt s ast1 cast_sort))
    (Expr cast_sort (AST_ZExt s ast2 cast_sort)).
Proof.
  intros s ast1 ast2 cast_sort H.
  apply EquivExpr.
  intros m.
  simpl.
  inversion H; subst.
  apply inj_pair2 in H2, H3.
  subst.
  specialize (H1 m).
  rewrite H1.
  reflexivity.
Qed.

Lemma equiv_smt_expr_sext : forall s (ast1 ast2 : smt_ast s) cast_sort,
  equiv_smt_expr (Expr s ast1) (Expr s ast2) ->
  equiv_smt_expr
    (Expr cast_sort (AST_SExt s ast1 cast_sort))
    (Expr cast_sort (AST_SExt s ast2 cast_sort)).
Proof.
  intros s ast1 ast2 cast_sort H.
  apply EquivExpr.
  intros m.
  simpl.
  inversion H; subst.
  apply inj_pair2 in H2, H3.
  subst.
  specialize (H1 m).
  rewrite H1.
  reflexivity.
Qed.

Lemma equiv_smt_expr_extract : forall s (ast1 ast2 : smt_ast s) cast_sort,
  equiv_smt_expr (Expr s ast1) (Expr s ast2) ->
  equiv_smt_expr
    (Expr cast_sort (AST_Extract s ast1 cast_sort))
    (Expr cast_sort (AST_Extract s ast2 cast_sort)).
Proof.
  intros s ast1 ast2 cast_sort H.
  apply EquivExpr.
  intros m.
  simpl.
  inversion H; subst.
  apply inj_pair2 in H2, H3.
  subst.
  specialize (H1 m).
  rewrite H1.
  reflexivity.
Qed.

Lemma equiv_smt_expr_ite : forall s (ast1 ast1' : smt_ast_bool) (ast2 ast2' ast3 ast3' : smt_ast s),
  equiv_smt_expr (Expr Sort_BV1 ast1) (Expr Sort_BV1 ast1') ->
  equiv_smt_expr (Expr s ast2) (Expr s ast2') ->
  equiv_smt_expr (Expr s ast3) (Expr s ast3') ->
  equiv_smt_expr
    (Expr s (AST_ITE s ast1 ast2 ast3))
    (Expr s (AST_ITE s ast1' ast2' ast3')).
Proof.
  intros s ast1 ast1' ast2 ast2' ast3 ast3' Heq1 Heq2 Heq3.
  apply EquivExpr.
  intros m.
  simpl.
  apply equiv_smt_expr_property with (m := m) in Heq1.
  apply equiv_smt_expr_property with (m := m) in Heq2.
  apply equiv_smt_expr_property with (m := m) in Heq3.
  rewrite Heq1, Heq2, Heq3.
  reflexivity.
Qed.

(* TODO: refactor *)
Lemma equiv_smt_expr_eq_symmetry : forall s (ast1 ast2 : smt_ast s),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_CmpOp s SMT_Eq ast1 ast2))
    (Expr Sort_BV1 (AST_CmpOp s SMT_Eq ast2 ast1)).
Proof.
  intros s ast1 ast2.
  apply EquivExpr.
  intros m.
  simpl.
  destruct s.
  {
    unfold smt_eval_cmpop_by_sort.
    rewrite Int1.eq_sym.
    reflexivity.
  }
  {
    unfold smt_eval_cmpop_by_sort.
    rewrite Int8.eq_sym.
    reflexivity.
  }
  {
    unfold smt_eval_cmpop_by_sort.
    rewrite Int16.eq_sym.
    reflexivity.
  }
  {
    unfold smt_eval_cmpop_by_sort.
    rewrite Int24.eq_sym.
    reflexivity.
  }
  {
    unfold smt_eval_cmpop_by_sort.
    rewrite Int32.eq_sym.
    reflexivity.
  }
  {
    unfold smt_eval_cmpop_by_sort.
    rewrite Int48.eq_sym.
    reflexivity.
  }
  {
    unfold smt_eval_cmpop_by_sort.
    rewrite Int56.eq_sym.
    reflexivity.
  }
  {
    unfold smt_eval_cmpop_by_sort.
    rewrite Int64.eq_sym.
    reflexivity.
  }
Qed.

(* TODO: rename *)
Lemma equiv_smt_expr_not_rewrite : forall (ast : smt_ast_bool),
  equiv_smt_expr
    (Expr Sort_BV1 (AST_Not Sort_BV1 ast))
    (Expr Sort_BV1 (AST_CmpOp Sort_BV1 SMT_Eq smt_ast_false ast)).
Proof.
  intros ast.
  apply EquivExpr.
  intros m.
  simpl.
  unfold smt_eval_cmpop_by_sort.
  remember (smt_eval_ast m Sort_BV1 ast) as b.
  pose proof (int1_destruct b) as L.
  destruct L as [L | L]; rewrite L; reflexivity.
Qed.

Lemma equiv_smt_expr_not_not : forall (ast : smt_ast_bool),
  equiv_smt_expr
    (Expr
      Sort_BV1
      (AST_Not Sort_BV1 (AST_Not Sort_BV1 ast)))
    (Expr Sort_BV1 ast).
Proof.
  intros ast.
  apply EquivExpr.
  intros m.
  simpl.
  unfold smt_eval_cmpop_by_sort.
  remember (smt_eval_ast m Sort_BV1 ast) as b.
  pose proof (int1_destruct b) as L.
  destruct L as [L | L]; rewrite L; reflexivity.
Qed.

Lemma equiv_smt_expr_de_morgan_and : forall (ast1 ast2 : smt_ast_bool),
  equiv_smt_expr
    (Expr
      Sort_BV1
      (AST_Not Sort_BV1 (AST_BinOp Sort_BV1 SMT_And ast1 ast2)))
    (Expr
      Sort_BV1
      (AST_BinOp Sort_BV1 SMT_Or (AST_Not Sort_BV1 ast1) (AST_Not Sort_BV1 ast2))).
Proof.
  intros ast1 ast2.
  apply EquivExpr.
  intros m.
  simpl.
  remember (smt_eval_ast m Sort_BV1 ast1) as b1.
  remember (smt_eval_ast m Sort_BV1 ast2) as b2.
  pose proof (int1_destruct b1) as L1.
  pose proof (int1_destruct b2) as L2.
  destruct L1 as [L1 | L1]; rewrite L1; destruct L2 as [L2 | L2]; rewrite L2; reflexivity.
Qed.

Lemma equiv_smt_expr_de_morgan_or : forall (ast1 ast2 : smt_ast_bool),
  equiv_smt_expr
    (Expr
      Sort_BV1
      (AST_Not Sort_BV1 (AST_BinOp Sort_BV1 SMT_Or ast1 ast2)))
    (Expr
      Sort_BV1
      (AST_BinOp Sort_BV1 SMT_And (AST_Not Sort_BV1 ast1) (AST_Not Sort_BV1 ast2))).
Proof.
  intros ast1 ast2.
  apply EquivExpr.
  intros m.
  simpl.
  remember (smt_eval_ast m Sort_BV1 ast1) as b1.
  remember (smt_eval_ast m Sort_BV1 ast2) as b2.
  pose proof (int1_destruct b1) as L1.
  pose proof (int1_destruct b2) as L2.
  destruct L1 as [L1 | L1]; rewrite L1; destruct L2 as [L2 | L2]; rewrite L2; reflexivity.
Qed.
