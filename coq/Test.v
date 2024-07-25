From Coq Require Import ZArith.
From Coq Require Import Strings.String.
From Coq Require Import List.
Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import CFG.
From SE Require Import Concrete.

(*
Definition x := DV_I8 (Int8.repr 1).
Definition y := DV_I8 (Int8.repr 2).
Definition a := DV_I32 (Int32.repr 1000).
Definition z := eval_ibinop (Add false true) x a.
*)

Definition f_id := (Name "f").

Definition f_dec := mk_declaration
  f_id
  (TYPE_Function ((TYPE_I 32)) [(TYPE_I 32); (TYPE_I 32)] false)
  ([], [[]; []])
  [(FNATTR_Attr_grp (0)%Z)]
  [ANN_preemption_specifier PREEMPTION_Dso_local; ANN_metadata [(METADATA_Id (Name "dbg")); (METADATA_Id (Anon (9)%Z))]]
.

Definition f_block_1_id := (Name "entry").
Definition f_block_2_id := (Name "if.then").
Definition f_block_3_id := (Name "if.else").
Definition f_block_4_id := (Name "return").

Definition f_block_1_cmd_0 := (CMD_Inst 0 (INSTR_Op (Name "cmp") (OP_ICmp Sgt (TYPE_I 32) (EXP_Ident (ID_Local (Name "x"))) (EXP_Ident (ID_Local (Name "y")))))).
Definition f_block_1_cmd_1 := (CMD_Term 1 (TERM_Br ((TYPE_I 1), (EXP_Ident (ID_Local (Name "cmp")))) f_block_2_id f_block_3_id)).

Definition f_block_1 : llvm_block := mk_block
  f_block_1_id
  [
    f_block_1_cmd_0;
    f_block_1_cmd_1
  ]
  None
.

Definition f_block_2_cmd_0 := (CMD_Inst 0 (INSTR_Op (Name "add") (OP_IBinop (LLVMAst.Add false true) (TYPE_I 32) (EXP_Ident (ID_Local (Name "x"))) (EXP_Ident (ID_Local (Name "y")))))).


Definition f_block_2 : llvm_block := mk_block
  f_block_2_id
  [f_block_2_cmd_0]
  None
.

Definition f_block_3_cmd_0 : llvm_cmd := (CMD_Term 0 (TERM_UnconditionalBr (Name "return"))).

Definition f_block_3 : llvm_block := mk_block
  f_block_3_id
  [f_block_3_cmd_0]
  None
.

Definition f_block_4_cmd_0 :=
  (CMD_Phi
    0
    (Phi
      (Name "retval.0")
      (TYPE_I 32)
      [
        (f_block_2_id, (EXP_Ident (ID_Local (Name "add"))));
        (f_block_3_id, (EXP_Integer (0)%Z))
      ]
    )
  ).

Definition f_block_4_cmd_1 := (CMD_Term 1 (TERM_Ret ((TYPE_I 32), (EXP_Ident (ID_Local (Name "retval.0")))))).

Definition f_block_4 := mk_block
  f_block_4_id
  [
    f_block_4_cmd_0;
    f_block_4_cmd_1
  ]
  None
.

Definition f_entry := (Name "entry").
Definition f_cfg : llvm_cfg := mkCFG
  f_entry
  [f_block_1; f_block_2; f_block_3; f_block_4]
  [(Name "x"); (Name "y")]
.

Definition f_def : llvm_definition := mk_definition
  _
  f_dec
  [(Name "x"); (Name "y")]
  f_cfg
.

Definition main_id := (Name "main").

Definition main_dec := mk_declaration
  main_id
  (TYPE_Function ((TYPE_I 32)) [] false)
  ([], [])
  [(FNATTR_Attr_grp (0)%Z)]
  [ANN_preemption_specifier PREEMPTION_Dso_local; ANN_metadata [(METADATA_Id (Name "dbg")); (METADATA_Id (Anon (26)%Z))]]
.

Definition main_block_1_cmd_0 :=
  (CMD_Inst
    0
    (INSTR_Call
      (Name "call")
      ((TYPE_I 32), (EXP_Ident (ID_Global f_id)))
      [(((TYPE_I 32), (EXP_Integer (1)%Z)), []); (((TYPE_I 32), (EXP_Integer (2)%Z)), [])]
      []
    )
  )
.

Definition main_block_1_id := (Name "entry").

Definition main_block_1_cmd_1 := (CMD_Term 1 (TERM_Ret ((TYPE_I 32), (EXP_Integer (0)%Z)))).

Definition main_block_1 : llvm_block := mk_block
  main_block_1_id
  [
    main_block_1_cmd_0;
    main_block_1_cmd_1
  ]
  None
.

Definition main_entry := (Name "entry").

Definition main_cfg : llvm_cfg := mkCFG
  main_entry
  [main_block_1]
  []
.

Definition main_def : llvm_definition := mk_definition
  _
  main_dec
  []
  main_cfg
.

Definition defs : list llvm_definition := [f_def; main_def].

Definition m : llvm_module := mk_module
  None
  None
  None
  []
  []
  []
  defs
.

Definition s_0 := mk_state
  (mk_inst_counter main_id main_entry 0)
  main_block_1_cmd_0
  [main_block_1_cmd_1]
  None
  empty_dv_store
  []
  empty_dv_store
  m
.

Definition final_state := mk_state
  (mk_inst_counter main_id main_entry 1)
  main_block_1_cmd_0
  []
  None
  empty_dv_store
  []
  empty_dv_store
  m
.

Lemma L_init : (init_state m main_def) = Some s_0.
Proof.
  reflexivity.
Qed.

Lemma L : multi_step s_0 final_state.
Proof.
Admitted.
