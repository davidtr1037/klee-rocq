From Coq Require Import ZArith.
From Coq Require Import Strings.String.
From Coq Require Import List.
Import ListNotations.
From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import ChoiceAxiom.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import ExecutionTreeOpt.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import ModuleAssumptions.
From SE Require Import Symbolic.
From SE Require Import ProofGeneration.
From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.
From SE.Utils Require Import Util.
Definition gs : smt_store := empty_smt_store.

Definition inst_0 : llvm_cmd := (CMD_Term 0 (TERM_UnconditionalBr (Name "while.cond"%string))).

Definition inst_1 : llvm_cmd := (CMD_Phi 1 (Phi (Name "n.0"%string) (TYPE_I 32) [((Name "entry"%string), (EXP_Integer (0)%Z)); ((Name "while.body"%string), (EXP_Ident (ID_Local (Name "inc"%string))))])).

Definition inst_2 : llvm_cmd := (CMD_Inst 2 (INSTR_Op (Name "cmp"%string) (OP_ICmp Slt (TYPE_I 32) (EXP_Ident (ID_Local (Name "n.0"%string))) (EXP_Integer (10)%Z)))).

Definition inst_3 : llvm_cmd := (CMD_Term 3 (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "cmp"%string)))) (Name "while.body"%string) (Name "while.end"%string))).

Definition inst_4 : llvm_cmd := (CMD_Inst 4 (INSTR_Op (Name "inc"%string) (OP_IBinop (LLVMAst.Add false false) (TYPE_I 32) (EXP_Ident (ID_Local (Name "n.0"%string))) (EXP_Integer (1)%Z)))).

Definition inst_5 : llvm_cmd := (CMD_Term 5 (TERM_UnconditionalBr (Name "while.cond"%string))).

Definition inst_6 : llvm_cmd := (CMD_Term 6 (TERM_Ret ((TYPE_I 32), (EXP_Integer (0)%Z)))).

Definition bb_0 : llvm_block := (mk_block (Name "entry"%string) [inst_0] None).

Definition bb_1 : llvm_block := (mk_block (Name "while.cond"%string) [inst_1; inst_2; inst_3] None).

Definition bb_2 : llvm_block := (mk_block (Name "while.body"%string) [inst_4; inst_5] None).

Definition bb_3 : llvm_block := (mk_block (Name "while.end"%string) [inst_6] None).

Definition decl_main : llvm_declaration := (mk_declaration (Name "main"%string) (TYPE_Function (TYPE_I 32) [] false) ([], [[]; []]) [] []).

Definition def_main : llvm_definition := (mk_definition _ decl_main [] (mk_cfg (Name "entry"%string) [bb_0; bb_1; bb_2; bb_3])).

Definition mdl : llvm_module := (mk_module None None None [] [] [] [def_main]).

Lemma is_supported_inst_0 : (is_supported_cmd inst_0).
Proof.
{
  apply IS_Term_UnconditionalBr.
}
Qed.

Lemma is_supported_inst_1 : (is_supported_cmd inst_1).
Proof.
{
  apply IS_Phi.
  intros bid e Hin.
  destruct Hin as [Hin | Hin].
  {
    inversion Hin.
    subst.
    {
      apply IS_EXP_Integer.
    }
  }
  destruct Hin as [Hin | Hin].
  {
    inversion Hin.
    subst.
    {
      apply IS_EXP_Ident.
    }
  }
  destruct Hin.
}
Qed.

Lemma is_supported_inst_2 : (is_supported_cmd inst_2).
Proof.
{
  apply IS_INSTR_Op.
  apply IS_OP_ICmp.
  {
    apply IS_EXP_Ident.
  }
  {
    apply IS_EXP_Integer.
  }
}
Qed.

Lemma is_supported_inst_3 : (is_supported_cmd inst_3).
Proof.
{
  apply IS_Term_Br.
  {
    apply IS_EXP_Ident.
  }
}
Qed.

Lemma is_supported_inst_4 : (is_supported_cmd inst_4).
Proof.
{
  apply IS_INSTR_Op.
  apply IS_OP_IBinop.
  {
    apply IS_EXP_Ident.
  }
  {
    apply IS_EXP_Integer.
  }
  {
    apply IS_Add.
  }
}
Qed.

Lemma is_supported_inst_5 : (is_supported_cmd inst_5).
Proof.
{
  apply IS_Term_UnconditionalBr.
}
Qed.

Lemma is_supported_inst_6 : (is_supported_cmd inst_6).
Proof.
{
  apply IS_Term_Ret.
  {
    apply IS_EXP_Integer.
  }
}
Qed.

Lemma is_supported_bb_0 : (is_supported_block (mk_block (Name "entry"%string) [inst_0] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_0.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_1 : (is_supported_block (mk_block (Name "while.cond"%string) [inst_1; inst_2; inst_3] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_1.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_2.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_3.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_2 : (is_supported_block (mk_block (Name "while.body"%string) [inst_4; inst_5] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_4.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_5.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_bb_3 : (is_supported_block (mk_block (Name "while.end"%string) [inst_6] None)).
Proof.
{
  apply IS_Block.
  apply IS_CmdList.
  intros c Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_inst_6.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_def_main : (is_supported_definition def_main).
Proof.
{
  apply IS_Definition.
  intros b Hin.
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_0.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_1.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_2.
  }
  destruct Hin as [Hin | Hin].
  {
    subst.
    apply is_supported_bb_3.
  }
  {
    destruct Hin.
  }
}
Qed.

Lemma is_supported_mdl : (is_supported_module mdl).
Proof.
{
  apply IS_Module.
  {
    intros g H.
    destruct H.
  }
  {
    intros d Hin.
    destruct Hin as [Hin | Hin].
    {
      subst.
      apply is_supported_def_main.
    }
    {
      destruct Hin.
    }
  }
}
Qed.

Definition s_0 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "entry"%string) 0) inst_0 [] None (empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_1 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "entry"%string)) (empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_2 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "entry"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_3 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "entry"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_4 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_5 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_6 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 0)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_7 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_8 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_9 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_10 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_11 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_12 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_13 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_14 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_15 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_16 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 2)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_17 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_18 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_19 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_20 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_21 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 3)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_22 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_23 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_24 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_25 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_26 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 4)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_27 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_28 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_29 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_30 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_31 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 5)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_32 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_33 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_34 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_35 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_36 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 6)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_37 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_38 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_39 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_40 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_41 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 7)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_42 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_43 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_44 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_45 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_46 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 8)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_47 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_48 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_49 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 4) inst_4 [inst_5] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_50 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.body"%string) 5) inst_5 [] (Some (Name "while.cond"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 10)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_51 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 1) inst_1 [inst_2; inst_3] (Some (Name "while.body"%string)) ((Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 10)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 9)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_52 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 2) inst_2 [inst_3] (Some (Name "while.body"%string)) ((Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 10)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 10)))); (Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 1)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_53 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.cond"%string) 3) inst_3 [] (Some (Name "while.body"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 0)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 10)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 10)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition s_54 : sym_state := (mk_sym_state (mk_inst_counter (Name "main"%string) (Name "while.end"%string) 6) inst_6 [] (Some (Name "while.cond"%string)) ((Name "cmp"%string) !-> Some ((Expr Sort_BV1 (AST_Const Sort_BV1 (Int1.repr 0)))); (Name "n.0"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 10)))); (Name "inc"%string) !-> Some ((Expr Sort_BV32 (AST_Const Sort_BV32 (Int32.repr 10)))); empty_smt_store) [] gs [] (AST_Const Sort_BV1 (Int1.repr 1)) mdl).

Definition t_54 : execution_tree := (t_leaf s_54).

Definition t_53 : execution_tree := (t_subtree s_53 [t_54]).

Definition t_52 : execution_tree := (t_subtree s_52 [t_53]).

Definition t_51 : execution_tree := (t_subtree s_51 [t_52]).

Definition t_50 : execution_tree := (t_subtree s_50 [t_51]).

Definition t_49 : execution_tree := (t_subtree s_49 [t_50]).

Definition t_48 : execution_tree := (t_subtree s_48 [t_49]).

Definition t_47 : execution_tree := (t_subtree s_47 [t_48]).

Definition t_46 : execution_tree := (t_subtree s_46 [t_47]).

Definition t_45 : execution_tree := (t_subtree s_45 [t_46]).

Definition t_44 : execution_tree := (t_subtree s_44 [t_45]).

Definition t_43 : execution_tree := (t_subtree s_43 [t_44]).

Definition t_42 : execution_tree := (t_subtree s_42 [t_43]).

Definition t_41 : execution_tree := (t_subtree s_41 [t_42]).

Definition t_40 : execution_tree := (t_subtree s_40 [t_41]).

Definition t_39 : execution_tree := (t_subtree s_39 [t_40]).

Definition t_38 : execution_tree := (t_subtree s_38 [t_39]).

Definition t_37 : execution_tree := (t_subtree s_37 [t_38]).

Definition t_36 : execution_tree := (t_subtree s_36 [t_37]).

Definition t_35 : execution_tree := (t_subtree s_35 [t_36]).

Definition t_34 : execution_tree := (t_subtree s_34 [t_35]).

Definition t_33 : execution_tree := (t_subtree s_33 [t_34]).

Definition t_32 : execution_tree := (t_subtree s_32 [t_33]).

Definition t_31 : execution_tree := (t_subtree s_31 [t_32]).

Definition t_30 : execution_tree := (t_subtree s_30 [t_31]).

Definition t_29 : execution_tree := (t_subtree s_29 [t_30]).

Definition t_28 : execution_tree := (t_subtree s_28 [t_29]).

Definition t_27 : execution_tree := (t_subtree s_27 [t_28]).

Definition t_26 : execution_tree := (t_subtree s_26 [t_27]).

Definition t_25 : execution_tree := (t_subtree s_25 [t_26]).

Definition t_24 : execution_tree := (t_subtree s_24 [t_25]).

Definition t_23 : execution_tree := (t_subtree s_23 [t_24]).

Definition t_22 : execution_tree := (t_subtree s_22 [t_23]).

Definition t_21 : execution_tree := (t_subtree s_21 [t_22]).

Definition t_20 : execution_tree := (t_subtree s_20 [t_21]).

Definition t_19 : execution_tree := (t_subtree s_19 [t_20]).

Definition t_18 : execution_tree := (t_subtree s_18 [t_19]).

Definition t_17 : execution_tree := (t_subtree s_17 [t_18]).

Definition t_16 : execution_tree := (t_subtree s_16 [t_17]).

Definition t_15 : execution_tree := (t_subtree s_15 [t_16]).

Definition t_14 : execution_tree := (t_subtree s_14 [t_15]).

Definition t_13 : execution_tree := (t_subtree s_13 [t_14]).

Definition t_12 : execution_tree := (t_subtree s_12 [t_13]).

Definition t_11 : execution_tree := (t_subtree s_11 [t_12]).

Definition t_10 : execution_tree := (t_subtree s_10 [t_11]).

Definition t_9 : execution_tree := (t_subtree s_9 [t_10]).

Definition t_8 : execution_tree := (t_subtree s_8 [t_9]).

Definition t_7 : execution_tree := (t_subtree s_7 [t_8]).

Definition t_6 : execution_tree := (t_subtree s_6 [t_7]).

Definition t_5 : execution_tree := (t_subtree s_5 [t_6]).

Definition t_4 : execution_tree := (t_subtree s_4 [t_5]).

Definition t_3 : execution_tree := (t_subtree s_3 [t_4]).

Definition t_2 : execution_tree := (t_subtree s_2 [t_3]).

Definition t_1 : execution_tree := (t_subtree s_1 [t_2]).

Definition t_0 : execution_tree := (t_subtree s_0 [t_1]).

Lemma UNSAT_10 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_9 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_8 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_7 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_6 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_5 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_4 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_3 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_2 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_1 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma UNSAT_0 : (unsat (AST_Const Sort_BV1 (Int1.repr 0))).
Proof.
Admitted.

Lemma L_54 : (safe_et_opt t_54).
Proof.
apply Safe_Leaf_Ret.
Qed.

Lemma L_53 : (safe_et_opt t_53).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_10.
      }
    }
    {
      left.
      exists (t_54).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_54.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_52 : (safe_et_opt t_52).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_53).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_53.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_51 : (safe_et_opt t_51).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_52).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_52.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_50 : (safe_et_opt t_50).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_51).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_51.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_49 : (safe_et_opt t_49).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_50).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_50.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_48 : (safe_et_opt t_48).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_49).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_49.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_9.
      }
    }
  }
}
Qed.

Lemma L_47 : (safe_et_opt t_47).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_48).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_48.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_46 : (safe_et_opt t_46).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_47).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_47.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_45 : (safe_et_opt t_45).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_46).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_46.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_44 : (safe_et_opt t_44).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_45).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_45.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_43 : (safe_et_opt t_43).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_44).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_44.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_8.
      }
    }
  }
}
Qed.

Lemma L_42 : (safe_et_opt t_42).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_43).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_43.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_41 : (safe_et_opt t_41).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_42).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_42.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_40 : (safe_et_opt t_40).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_41).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_41.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_39 : (safe_et_opt t_39).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_40).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_40.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_38 : (safe_et_opt t_38).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_39).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_39.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_7.
      }
    }
  }
}
Qed.

Lemma L_37 : (safe_et_opt t_37).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_38).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_38.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_36 : (safe_et_opt t_36).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_37).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_37.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_35 : (safe_et_opt t_35).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_36).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_36.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_34 : (safe_et_opt t_34).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_35).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_35.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_33 : (safe_et_opt t_33).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_34).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_34.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_6.
      }
    }
  }
}
Qed.

Lemma L_32 : (safe_et_opt t_32).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_33).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_33.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_31 : (safe_et_opt t_31).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_32).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_32.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_30 : (safe_et_opt t_30).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_31).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_31.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_29 : (safe_et_opt t_29).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_30).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_30.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_28 : (safe_et_opt t_28).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_29).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_29.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_5.
      }
    }
  }
}
Qed.

Lemma L_27 : (safe_et_opt t_27).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_28).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_28.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_26 : (safe_et_opt t_26).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_27).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_27.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_25 : (safe_et_opt t_25).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_26).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_26.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_24 : (safe_et_opt t_24).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_25).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_25.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_23 : (safe_et_opt t_23).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_24).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_24.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_4.
      }
    }
  }
}
Qed.

Lemma L_22 : (safe_et_opt t_22).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_23).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_23.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_21 : (safe_et_opt t_21).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_22).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_22.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_20 : (safe_et_opt t_20).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_21).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_21.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_19 : (safe_et_opt t_19).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_20).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_20.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_18 : (safe_et_opt t_18).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_19).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_19.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_3.
      }
    }
  }
}
Qed.

Lemma L_17 : (safe_et_opt t_17).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_18).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_18.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_16 : (safe_et_opt t_16).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_17).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_17.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_15 : (safe_et_opt t_15).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_16).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_16.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_14 : (safe_et_opt t_14).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_15).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_15.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_13 : (safe_et_opt t_13).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_14).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_14.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_2.
      }
    }
  }
}
Qed.

Lemma L_12 : (safe_et_opt t_12).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_13).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_13.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_11 : (safe_et_opt t_11).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_12).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_12.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_10 : (safe_et_opt t_10).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_11).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_11.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_9 : (safe_et_opt t_9).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_10).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_10.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "n.0"%string), _); ((Name "cmp"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_8 : (safe_et_opt t_8).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
    {
      left.
      exists (t_9).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_9.
        }
        {
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_1.
      }
    }
  }
}
Qed.

Lemma L_7 : (safe_et_opt t_7).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_8).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_8.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "inc"%string), _); ((Name "n.0"%string), _)])).
            inversion H13.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_6 : (safe_et_opt t_6).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_7).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_7.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_optimized_update (_) (_) (_) (_) (_) ([((Name "cmp"%string), _); ((Name "inc"%string), _)])).
            inversion H14.
            subst.
            apply equiv_smt_expr_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_5 : (safe_et_opt t_5).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_6).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_6.
        }
        {
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_4 : (safe_et_opt t_4).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
    {
      left.
      exists (t_5).
      split.
      {
        simpl.
        left.
        reflexivity.
      }
      {
        split.
        {
          apply L_5.
        }
        {
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_update (_) (_) (_) (_) (_) (H13)).
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_3 : (safe_et_opt t_3).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_br.
  }
  {
    intros s Hstep.
    inversion Hstep.
    subst.
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
          inversion H13.
          subst.
          inversion H14.
          subst.
          inversion H15.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply injection_some in H12.
            apply injection_ast in H12.
            subst.
            apply equiv_smt_expr_normalize_simplify.
          }
        }
      }
    }
    {
      right.
      apply Unsat_State.
      inversion H12.
      apply (equiv_smt_expr_unsat ((AST_Const Sort_BV1 (Int1.repr 0))) (_)).
      {
        apply equiv_smt_expr_symmetry.
        apply injection_some in H12.
        apply injection_ast in H12.
        subst.
        apply equiv_smt_expr_normalize_simplify.
      }
      {
        apply UNSAT_0.
      }
    }
  }
}
Qed.

Lemma L_2 : (safe_et_opt t_2).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_instr_op.
  }
  {
    intros s Hstep.
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
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            apply (equiv_smt_store_on_update (_) (_) (_) (_) (_) (H13)).
            apply equiv_smt_expr_normalize_simplify.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_1 : (safe_et_opt t_1).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_phi.
  }
  {
    intros s Hstep.
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
          inversion Hstep.
          subst.
          apply EquivSymState.
          {
            inversion H14.
            subst.
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma L_0 : (safe_et_opt t_0).
Proof.
{
  apply Safe_Subtree.
  {
    apply not_error_unconditional_br.
  }
  {
    intros s Hstep.
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
          inversion Hstep.
          subst.
          inversion H10.
          subst.
          inversion H11.
          subst.
          inversion H12.
          subst.
          apply EquivSymState.
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_sym_stack_refl.
          }
          {
            apply equiv_smt_store_refl.
          }
          {
            apply equiv_smt_expr_refl.
          }
        }
      }
    }
  }
}
Qed.

Lemma program_safety : (is_safe_program mdl (Name "main"%string)).
Proof.
{
  destruct t_0 as [r | r l] eqn:E.
  {
    discriminate E.
  }
  {
    apply (completeness_via_et (mdl) ((Name "main"%string)) (s_0) (l)).
    {
      apply is_supported_mdl.
    }
    {
      reflexivity.
    }
    {
      inversion E.
      subst.
      rewrite <- E.
      apply L_0.
    }
  }
}
Qed.

