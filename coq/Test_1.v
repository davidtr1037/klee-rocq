From Coq Require  Import ZArith.
From Coq Require  Import Strings.String.
From Coq Require  Import List.
Import ListNotations.
From SE Require  Import BitVectors.
From SE Require  Import CFG.
From SE Require  Import Concrete.
From SE Require  Import DynamicValue.
From SE Require  Import ExecutionTreeOpt.
From SE Require  Import IDMap.
From SE Require  Import LLVMAst.
From SE Require  Import Symbolic.
From SE Require  Import ProofGeneration.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

Definition inst_0 : llvm_cmd :=
  (CMD_Inst
    0
    (INSTR_Op
      (Name
        "add"%string
      )
      (OP_IBinop
        (LLVMAst.Add
          false
          false
        )
        (TYPE_I
          32
        )
        (EXP_Integer
          (1)%Z
        )
        (EXP_Integer
          (2)%Z
        )
      )
    )
  ).

Definition inst_1 : llvm_cmd :=
  (CMD_Inst
    1
    (INSTR_Op
      (Name
        "add1"%string
      )
      (OP_IBinop
        (LLVMAst.Add
          false
          false
        )
        (TYPE_I
          32
        )
        (EXP_Ident
          (ID_Local
            (Name
              "add"%string
            )
          )
        )
        (EXP_Integer
          (7)%Z
        )
      )
    )
  ).

Definition inst_2 : llvm_cmd :=
  (CMD_Term
    2
    (TERM_Ret
      (
        (TYPE_I
          32
        ),
        (EXP_Ident
          (ID_Local
            (Name
              "add1"%string
            )
          )
        )
      )
    )
  ).

Definition bb_0 : llvm_block :=
  (mk_block
    (Name
      "entry"%string
    )
    [
      inst_0;
      inst_1;
      inst_2
    ]
    None
  ).

Definition def_0 : llvm_definition :=
  (mk_definition
    _
    (mk_declaration
      (Name
        "main"%string
      )
      (TYPE_Function
        (TYPE_I
          32
        )
        []
        false
      )
      (
        [],
        [
          [];
          []
        ]
      )
      []
      []
    )
    []
    (mk_cfg
      (Name
        "entry"%string
      )
      [
        bb_0
      ]
    )
  ).

Definition mdl : llvm_module :=
  (mk_module
    None
    None
    None
    []
    []
    []
    [
      def_0
    ]
  ).

Definition gs := empty_smt_store.

Definition s_ls_0 := empty_smt_store.
Definition s_symbolics_0 : list string := [].
Definition s_pc_0 := SMT_True.
Definition s_0 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "entry") 0)
  inst_0
  [inst_1; inst_2]
  None
  s_ls_0
  []
  gs
  s_symbolics_0
  s_pc_0
  mdl
.

Definition s_ls_1 := ((Name "add") !-> Some (SMT_Const_I32 (Int32.repr 3)); empty_smt_store).
Definition s_symbolics_1 : list string := [].
Definition s_pc_1 := SMT_True.
Definition s_1 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "entry") 1)
  inst_1
  [inst_2]
  None
  s_ls_1
  []
  gs
  s_symbolics_1
  s_pc_1
  mdl
.

Definition s_ls_2 := ((Name "add1") !-> Some (SMT_Const_I32 (Int32.repr 10)); s_ls_1).
Definition s_symbolics_2 : list string := [].
Definition s_pc_2 := SMT_True.
Definition s_2 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "entry") 2)
  inst_2
  []
  None
  s_ls_2
  []
  gs
  s_symbolics_2
  s_pc_2
  mdl
.

Definition t_2 := t_leaf s_2.
Definition t_1 := t_subtree s_1 [t_2].
Definition t_0 := t_subtree s_0 [t_1].

Lemma L_2 : safe_et_opt t_2.
Proof.
apply Safe_Leaf_Ret.
Qed.

Lemma L_1 : safe_et_opt t_1.
Proof.
{
  apply Safe_Subtree.
  {
    apply LAUX_not_error_instr_op.
  }
  {
    intros s Hse.
    {
      left.
      exists (t_2).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_2.
        }
        {
          simpl.
          inversion Hse; subst.
          apply EquivSymState.
          {
            simpl in H13.
            apply (LAUX_1 _ _ _ _ _ H13).
            { admit. } (* simplify lemma *)
          }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
      }
    }
  }
}
Admitted.

Lemma L_0 : safe_et_opt t_0.
Proof.
{
  Print s_0. Print inst_0.
  apply Safe_Subtree.
  {
    apply LAUX_not_error_instr_op.
  }
  {
    intros s Hse.
    {
      left.
      exists (t_1).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_1.
        }
        {
          simpl.
          inversion Hse; subst.
          apply EquivSymState.
          {
            simpl in H13.
            apply (LAUX_1 _ _ _ _ _ H13).
            admit. (* simplify lemma *)
          }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
      }
    }
  }
}
Admitted.

Theorem program_safe : is_safe_program mdl (Name "main").
Proof.
{
  destruct t_0 as [r | r l] eqn:E.
  {
    discriminate E.
  }
  {
    apply completeness_via_et with (init_s := s_0) (l := l).
    { admit. }
    { reflexivity. }
    {
      inversion E; subst.
      rewrite <- E.
      apply L_0.
    }
  }
}
Admitted.