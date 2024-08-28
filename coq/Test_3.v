From Coq Require Import ZArith.
From Coq Require Import Strings.String.
From Coq Require Import List.
Import ListNotations.
From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import ExecutionTreeOpt.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import Symbolic.
From SE Require Import ProofGeneration.
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
        (EXP_Ident
          (ID_Local
            (Name
              "x"%string
            )
          )
        )
        (EXP_Ident
          (ID_Local
            (Name
              "y"%string
            )
          )
        )
      )
    )
  ).

Definition inst_1 : llvm_cmd :=
  (CMD_Term
    1
    (TERM_Ret
      (
        (TYPE_I
          32
        ),
        (EXP_Ident
          (ID_Local
            (Name
              "add"%string
            )
          )
        )
      )
    )
  ).

Definition inst_2 : llvm_cmd :=
  (CMD_Inst
    2
    (INSTR_Op
      (Name
        "inc"%string
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
          (1)%Z
        )
      )
    )
  ).

Definition inst_3 : llvm_cmd :=
  (CMD_Inst
    3
    (INSTR_Call
      (Name
        "call"%string
      )
      (
        (TYPE_I
          32
        ),
        (EXP_Ident
          (ID_Global
            (Name
              "foo"%string
            )
          )
        )
      )
      [
        (
          (
            (TYPE_I
              32
            ),
            (EXP_Ident
              (ID_Local
                (Name
                  "inc"%string
                )
              )
            )
          ),
          []
        );
        (
          (
            (TYPE_I
              32
            ),
            (EXP_Integer
              (1)%Z
            )
          ),
          []
        )
      ]
      []
    )
  ).

Definition inst_4 : llvm_cmd :=
  (CMD_Term
    4
    (TERM_Ret
      (
        (TYPE_I
          32
        ),
        (EXP_Ident
          (ID_Local
            (Name
              "call"%string
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
      inst_1
    ]
    None
  ).

Definition bb_1 : llvm_block :=
  (mk_block
    (Name
      "entry"%string
    )
    [
      inst_2;
      inst_3;
      inst_4
    ]
    None
  ).

Definition def_0 : llvm_definition :=
  (mk_definition
    _
    (mk_declaration
      (Name
        "foo"%string
      )
      (TYPE_Function
        (TYPE_I
          32
        )
        [
          (TYPE_I
            32
          );
          (TYPE_I
            32
          )
        ]
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
    [
      (Name
        "x"%string
      );
      (Name
        "y"%string
      )
    ]
    (mk_cfg
      (Name
        "entry"%string
      )
      [
        bb_0
      ]
    )
  ).

Definition def_1 : llvm_definition :=
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
        bb_1
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
      def_0;
      def_1
    ]
  ).

Definition gs := empty_smt_store.

Definition s_ls_0 := empty_smt_store.
Definition s_stk_0 : list sym_frame := [].
Definition s_symbolics_0 : list string := [].
Definition s_pc_0 := SMT_True.
Definition s_0 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "entry") 2)
  inst_2
  [inst_3; inst_4]
  None
  s_ls_0
  s_stk_0
  gs
  s_symbolics_0
  s_pc_0
  mdl
.

Definition s_ls_1 := ((Name "inc") !-> Some (SMT_Const_I32 (Int32.repr 2)); s_ls_0).
Definition s_stk_1 := s_stk_0.
Definition s_symbolics_1 : list string := [].
Definition s_pc_1 := SMT_True.
Definition s_1 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "entry") 3)
  inst_3
  [inst_4]
  None
  s_ls_1
  s_stk_1
  gs
  s_symbolics_1
  s_pc_1
  mdl
.

Definition s_ls_2 :=
  (
    (Name "x") !-> Some (SMT_Const_I32 (Int32.repr 2));
    (Name "y") !-> Some (SMT_Const_I32 (Int32.repr 1));
    empty_smt_store
  ).
Definition s_sym_frame_2 :=
  (Sym_Frame s_ls_1 (mk_inst_counter (Name "main") (Name "entry") 4) None (Some (Name "call"))).
Definition s_stk_2 := s_sym_frame_2 :: s_stk_1.
Definition s_symbolics_2 : list string := [].
Definition s_pc_2 := SMT_True.
Definition s_2 := mk_sym_state
  (mk_inst_counter (Name "foo") (Name "entry") 0)
  inst_0
  [inst_1]
  None
  s_ls_2
  s_stk_2
  gs
  s_symbolics_2
  s_pc_2
  mdl
.

Definition s_ls_3 := ((Name "add") !-> Some (SMT_Const_I32 (Int32.repr 3)); s_ls_2).
Definition s_stk_3 := s_stk_2.
Definition s_symbolics_3 : list string := [].
Definition s_pc_3 := SMT_True.
Definition s_3 := mk_sym_state
  (mk_inst_counter (Name "foo") (Name "entry") 1)
  inst_1
  []
  None
  s_ls_3
  s_stk_3
  gs
  s_symbolics_3
  s_pc_3
  mdl
.

Definition s_ls_4 := ((Name "call") !-> Some (SMT_Const_I32 (Int32.repr 3)); s_ls_1).
Definition s_stk_4 := s_stk_1.
Definition s_symbolics_4 : list string := [].
Definition s_pc_4 := SMT_True.
Definition s_4 := mk_sym_state
  (mk_inst_counter (Name "main") (Name "entry") 4)
  inst_4
  []
  None
  s_ls_4
  s_stk_4
  gs
  s_symbolics_4
  s_pc_4
  mdl
.

Definition t_4 := t_leaf s_4.
Definition t_3 := t_subtree s_3 [t_4].
Definition t_2 := t_subtree s_2 [t_3].
Definition t_1 := t_subtree s_1 [t_2].
Definition t_0 := t_subtree s_0 [t_1].

Lemma L_4 : safe_et_opt t_4.
Proof.
apply Safe_Leaf_Ret.
Qed.

Lemma L_3 : safe_et_opt t_3.
Proof.
{
  apply Safe_Subtree.
  {
    apply LAUX_not_error_ret.
  }
  {
    intros s Hse.
    {
      left.
      exists (t_4).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_4.
        }
        {
          simpl.
          inversion Hse; subst.
          (* TODO: add specific lemma *)
          inversion H16; subst.
          inversion H17; subst.
          apply EquivSymState.
          {
            simpl in H15.
            (* TODO: avoid *)
            inversion H15; subst.
            apply equiv_smt_store_refl.
          }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
      }
    }
  }
}
Qed.

Lemma L_2 : safe_et_opt t_2.
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
      exists (t_3).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_3.
        }
        {
          simpl.
          inversion Hse; subst.
          apply EquivSymState.
          {
            simpl in H13.
            apply LAUX_1 with
              (se1 := (SMT_BinOp SMT_Add (SMT_Const_I32 (Int32.repr 2)) (SMT_Const_I32 (Int32.repr 1))))
              (se2 := se).
            { assumption. }
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

Lemma L_1 : safe_et_opt t_1.
Proof.
{
  apply Safe_Subtree.
  {
    apply LAUX_not_error_call.
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
          (* TODO: add specific lemma *)
          inversion H16; subst.
          inversion H18; subst.
          inversion H19; subst.
          apply EquivSymState.
          {
            (* TODO: avoid *)
            inversion H20; subst.
            apply equiv_smt_store_refl.
          }
          { apply equiv_sym_stack_refl. }
          { apply equiv_smt_store_refl. }
          { apply equiv_smt_expr_refl. }
        }
      }
    }
  }
}
Qed.

Lemma L_0 : safe_et_opt t_0.
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
            apply LAUX_1 with
              (se1 := (SMT_BinOp SMT_Add (SMT_Const_I32 (Int32.repr 1)) (SMT_Const_I32 (Int32.repr 1))))
              (se2 := se).
            { assumption. }
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
