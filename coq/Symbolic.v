From Coq Require Import List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import ChoiceAxiom.
From SE Require Import Concrete.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import Relation.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

From SE.Utils Require Import IDMap.
From SE.Utils Require Import ListUtil.
From SE.Utils Require Import Util.

Definition smt_store := total_map (option smt_expr).

Definition empty_smt_store : smt_store := empty_map None.

Inductive sym_frame : Type :=
  | Sym_Frame (s : smt_store) (ic : inst_counter) (pbid : option block_id) (v : option raw_id)
.

(* TODO: define as an inductive type? *)
Record sym_state : Type := mk_sym_state {
  sym_ic : inst_counter;
  sym_cmd : llvm_cmd;
  sym_block : list llvm_cmd;
  sym_prev_bid : option block_id;
  sym_store : smt_store;
  sym_stack : list sym_frame;
  sym_globals : smt_store;
  sym_symbolics : list string;
  sym_pc : smt_ast_bool;
  sym_module : llvm_module;
}.

Inductive sat_sym_state : smt_model -> sym_state -> Prop :=
  | Sat_State: forall m ic c cs pbid ls stk gs syms pc mdl,
      sat_via pc m ->
      sat_sym_state m (mk_sym_state ic c cs pbid ls stk gs syms pc mdl)
.

Inductive unsat_sym_state : sym_state -> Prop :=
  | Unsat_State: forall ic c cs pbid ls stk gs syms pc mdl,
      unsat pc ->
      unsat_sym_state (mk_sym_state ic c cs pbid ls stk gs syms pc mdl)
.

Definition sym_lookup_ident (s : smt_store) (g : smt_store) (id : ident) : option smt_expr :=
  match id with
  | ID_Local x => s x
  | ID_Global x => g x
  end
.

Definition sym_eval_ident (s : smt_store) (g : smt_store) (ot : option typ) (id : ident) : option smt_expr :=
  match ot with
  | Some t =>
    match (sym_lookup_ident s g id) with
    | Some se =>
        match t, se with
        | TYPE_I 1, Expr Sort_BV1 ast => Some se
        | TYPE_I 8, Expr Sort_BV8 ast => Some se
        | TYPE_I 16, Expr Sort_BV16 ast => Some se
        | TYPE_I 32, Expr Sort_BV32 ast => Some se
        | TYPE_I 64, Expr Sort_BV64 ast => Some se
        | _, _ => None
        end
    | None => None
    end
  | None => sym_lookup_ident s g id
  end
.

Definition ibinop_to_smt_binop (op : ibinop) : smt_binop :=
  match op with
  | Add _ _ => SMT_Add
  | Sub _ _=> SMT_Sub
  | Mul _ _=> SMT_Mul
  | Shl _ _=> SMT_Shl
  | UDiv _ => SMT_UDiv
  | SDiv _ => SMT_SDiv
  | LShr _ => SMT_LShr
  | AShr _ => SMT_AShr
  | URem => SMT_URem
  | SRem => SMT_SRem
  | And => SMT_And
  | Or => SMT_Or
  | Xor => SMT_Xor
  end
.

Definition sym_eval_ibinop (op : ibinop) (e1 e2 : smt_expr) : option smt_expr :=
  match e1, e2 with
  | (Expr Sort_BV1 ast1), (Expr Sort_BV1 ast2) =>
      Some (Expr Sort_BV1 (AST_BinOp Sort_BV1 (ibinop_to_smt_binop op) ast1 ast2))
  | (Expr Sort_BV8 ast1), (Expr Sort_BV8 ast2) =>
      Some (Expr Sort_BV8 (AST_BinOp Sort_BV8 (ibinop_to_smt_binop op) ast1 ast2))
  | (Expr Sort_BV16 ast1), (Expr Sort_BV16 ast2) =>
      Some (Expr Sort_BV16 (AST_BinOp Sort_BV16 (ibinop_to_smt_binop op) ast1 ast2))
  | (Expr Sort_BV32 ast1), (Expr Sort_BV32 ast2) =>
      Some (Expr Sort_BV32 (AST_BinOp Sort_BV32 (ibinop_to_smt_binop op) ast1 ast2))
  | (Expr Sort_BV64 ast1), (Expr Sort_BV64 ast2) =>
      Some (Expr Sort_BV64 (AST_BinOp Sort_BV64 (ibinop_to_smt_binop op) ast1 ast2))
  | _, _ => None
  end
.

Definition icmp_to_smt_cmpop (op : icmp) : smt_cmpop :=
  match op with
  | Eq => SMT_Eq
  | Ne => SMT_Ne
  | Ugt => SMT_Ugt
  | Uge => SMT_Uge
  | Ult => SMT_Ult
  | Ule => SMT_Ule
  | Sgt => SMT_Sgt
  | Sge => SMT_Sge
  | Slt => SMT_Slt
  | Sle => SMT_Sle
  end
.

Definition sym_eval_icmp (op : icmp) (e1 e2 : smt_expr) : option smt_expr :=
  match e1, e2 with
  | (Expr Sort_BV1 ast1), (Expr Sort_BV1 ast2) =>
      Some (Expr Sort_BV1 (AST_CmpOp Sort_BV1 (icmp_to_smt_cmpop op) ast1 ast2))
  | (Expr Sort_BV8 ast1), (Expr Sort_BV8 ast2) =>
      Some (Expr Sort_BV1 (AST_CmpOp Sort_BV8 (icmp_to_smt_cmpop op) ast1 ast2))
  | (Expr Sort_BV16 ast1), (Expr Sort_BV16 ast2) =>
      Some (Expr Sort_BV1 (AST_CmpOp Sort_BV16 (icmp_to_smt_cmpop op) ast1 ast2))
  | (Expr Sort_BV32 ast1), (Expr Sort_BV32 ast2) =>
      Some (Expr Sort_BV1 (AST_CmpOp Sort_BV32 (icmp_to_smt_cmpop op) ast1 ast2))
  | (Expr Sort_BV64 ast1), (Expr Sort_BV64 ast2) =>
      Some (Expr Sort_BV1 (AST_CmpOp Sort_BV64 (icmp_to_smt_cmpop op) ast1 ast2))
  | _, _ => None
  end
.

Definition sym_eval_convert (conv : conversion_type) t1 (e : smt_expr) t2 : option smt_expr :=
  match conv with
  | Zext =>
      match t1, t2 with
      | TYPE_I w1, TYPE_I w2 =>
          match w1, e, w2 with
          (* i8 *)
          | 1%positive, (Expr Sort_BV1 ast), 8%positive => Some (Expr Sort_BV8 (AST_ZExt Sort_BV1 ast Sort_BV8))
          (* i16 *)
          | 1%positive, (Expr Sort_BV1 ast), 16%positive => Some (Expr Sort_BV16 (AST_ZExt Sort_BV1 ast Sort_BV16))
          | 8%positive, (Expr Sort_BV8 ast), 16%positive => Some (Expr Sort_BV16 (AST_ZExt Sort_BV8 ast Sort_BV16))
          (* i32 *)
          | 1%positive, (Expr Sort_BV1 ast), 32%positive => Some (Expr Sort_BV32 (AST_ZExt Sort_BV1 ast Sort_BV32))
          | 8%positive, (Expr Sort_BV8 ast), 32%positive => Some (Expr Sort_BV32 (AST_ZExt Sort_BV8 ast Sort_BV32))
          | 16%positive, (Expr Sort_BV16 ast), 32%positive => Some (Expr Sort_BV32 (AST_ZExt Sort_BV16 ast Sort_BV32))
          (* i64 *)
          | 1%positive, (Expr Sort_BV1 ast), 64%positive => Some (Expr Sort_BV64 (AST_ZExt Sort_BV1 ast Sort_BV64))
          | 8%positive, (Expr Sort_BV8 ast), 64%positive => Some (Expr Sort_BV64 (AST_ZExt Sort_BV8 ast Sort_BV64))
          | 16%positive, (Expr Sort_BV16 ast), 64%positive => Some (Expr Sort_BV64 (AST_ZExt Sort_BV16 ast Sort_BV64))
          | 32%positive, (Expr Sort_BV32 ast), 64%positive => Some (Expr Sort_BV64 (AST_ZExt Sort_BV32 ast Sort_BV64))
          | _, _, _ => None
          end
      | _, _ => None
      end
  | Sext =>
      match t1, t2 with
      | TYPE_I w1, TYPE_I w2 =>
          match w1, e, w2 with
          (* i8 *)
          | 1%positive, (Expr Sort_BV1 ast), 8%positive => Some (Expr Sort_BV8 (AST_SExt Sort_BV1 ast Sort_BV8))
          (* i16 *)
          | 1%positive, (Expr Sort_BV1 ast), 16%positive => Some (Expr Sort_BV16 (AST_SExt Sort_BV1 ast Sort_BV16))
          | 8%positive, (Expr Sort_BV8 ast), 16%positive => Some (Expr Sort_BV16 (AST_SExt Sort_BV8 ast Sort_BV16))
          (* i32 *)
          | 1%positive, (Expr Sort_BV1 ast), 32%positive => Some (Expr Sort_BV32 (AST_SExt Sort_BV1 ast Sort_BV32))
          | 8%positive, (Expr Sort_BV8 ast), 32%positive => Some (Expr Sort_BV32 (AST_SExt Sort_BV8 ast Sort_BV32))
          | 16%positive, (Expr Sort_BV16 ast), 32%positive => Some (Expr Sort_BV32 (AST_SExt Sort_BV16 ast Sort_BV32))
          (* i64 *)
          | 1%positive, (Expr Sort_BV1 ast), 64%positive => Some (Expr Sort_BV64 (AST_SExt Sort_BV1 ast Sort_BV64))
          | 8%positive, (Expr Sort_BV8 ast), 64%positive => Some (Expr Sort_BV64 (AST_SExt Sort_BV8 ast Sort_BV64))
          | 16%positive, (Expr Sort_BV16 ast), 64%positive => Some (Expr Sort_BV64 (AST_SExt Sort_BV16 ast Sort_BV64))
          | 32%positive, (Expr Sort_BV32 ast), 64%positive => Some (Expr Sort_BV64 (AST_SExt Sort_BV32 ast Sort_BV64))
          | _, _, _ => None
          end
      | _, _ => None
      end
  | Trunc =>
      match t1, t2 with
      | TYPE_I w1, TYPE_I w2 =>
          match w1, e, w2 with
          (* i1 *)
          | 8%positive, (Expr Sort_BV8 ast), 1%positive => Some (Expr Sort_BV1 (AST_Extract Sort_BV8 ast Sort_BV1))
          | 16%positive, (Expr Sort_BV16 ast), 1%positive => Some (Expr Sort_BV1 (AST_Extract Sort_BV16 ast Sort_BV1))
          | 32%positive, (Expr Sort_BV32 ast), 1%positive => Some (Expr Sort_BV1 (AST_Extract Sort_BV32 ast Sort_BV1))
          | 64%positive, (Expr Sort_BV64 ast), 1%positive => Some (Expr Sort_BV1 (AST_Extract Sort_BV64 ast Sort_BV1))
          (* i8 *)
          | 16%positive, (Expr Sort_BV16 ast), 8%positive => Some (Expr Sort_BV8 (AST_Extract Sort_BV16 ast Sort_BV8))
          | 32%positive, (Expr Sort_BV32 ast), 8%positive => Some (Expr Sort_BV8 (AST_Extract Sort_BV32 ast Sort_BV8))
          | 64%positive, (Expr Sort_BV64 ast), 8%positive => Some (Expr Sort_BV8 (AST_Extract Sort_BV64 ast Sort_BV8))
          (* i16 *)
          | 32%positive, (Expr Sort_BV32 ast), 16%positive => Some (Expr Sort_BV16 (AST_Extract Sort_BV32 ast Sort_BV16))
          | 64%positive, (Expr Sort_BV64 ast), 16%positive => Some (Expr Sort_BV16 (AST_Extract Sort_BV64 ast Sort_BV16))
          (* i32 *)
          | 64%positive, (Expr Sort_BV64 ast), 32%positive => Some (Expr Sort_BV32 (AST_Extract Sort_BV64 ast Sort_BV32))
          | _, _, _ => None
          end
      | _, _ => None
      end
  | Bitcast =>
      match t1, t2 with
      | TYPE_I w1, TYPE_I w2 =>
        if (w1 =? w2)%positive then Some e else None
      | _, _ => None
      end
  end
.

Definition sym_eval_ite (e1 e2 e3 : smt_expr) : option smt_expr :=
  match e1 with
  | (Expr Sort_BV1 ast1) =>
      match e2, e3 with
      | (Expr Sort_BV1 ast2), (Expr Sort_BV1 ast3) =>
          Some (Expr Sort_BV1 (AST_ITE Sort_BV1 ast1 ast2 ast3))
      | (Expr Sort_BV8 ast2), (Expr Sort_BV8 ast3) =>
          Some (Expr Sort_BV8 (AST_ITE Sort_BV8 ast1 ast2 ast3))
      | (Expr Sort_BV16 ast2), (Expr Sort_BV16 ast3) =>
          Some (Expr Sort_BV16 (AST_ITE Sort_BV16 ast1 ast2 ast3))
      | (Expr Sort_BV32 ast2), (Expr Sort_BV32 ast3) =>
          Some (Expr Sort_BV32 (AST_ITE Sort_BV32 ast1 ast2 ast3))
      | (Expr Sort_BV64 ast2), (Expr Sort_BV64 ast3) =>
          Some (Expr Sort_BV64 (AST_ITE Sort_BV64 ast1 ast2 ast3))
      | _, _ => None
      end
  | _ => None
  end
.

Fixpoint sym_eval_exp (s : smt_store) (g : smt_store) (t : option typ) (e : llvm_exp) : option smt_expr :=
  match e with
  | EXP_Ident id => sym_eval_ident s g t id
  | EXP_Integer n =>
      match t with
      | Some (TYPE_I bits) => make_smt_const bits n
      | _ => None
      end
  | EXP_Bool b => Some (make_smt_bool b)
  | EXP_Null => None
  | EXP_Zero_initializer => None
  | EXP_Undef => None
  | EXP_Poison => None
  | OP_IBinop op t v1 v2 =>
      match (sym_eval_exp s g (Some t) v1, sym_eval_exp s g (Some t) v2) with
      | (Some e1, Some e2) => sym_eval_ibinop op e1 e2
      | (_, _) => None
      end
  | OP_ICmp op t v1 v2 =>
      match (sym_eval_exp s g (Some t) v1, sym_eval_exp s g (Some t) v2) with
      | (Some e1, Some e2) => sym_eval_icmp op e1 e2
      | (_, _) => None
      end
  | OP_Conversion conv t1 v t2 =>
      match (sym_eval_exp s g (Some t1) v) with
      | Some e => sym_eval_convert conv t1 e t2
      | _ => None
      end
  | OP_Select t1 v1 t2 v2 t3 v3 =>
      match (sym_eval_exp s g (Some t1) v1,
             sym_eval_exp s g (Some t2) v2,
             sym_eval_exp s g (Some t3) v3) with
      | (Some e1, Some e2, Some e3) =>
          sym_eval_ite e1 e2 e3
      | _ => None
      end
  end
.

Definition sym_eval_constant_exp (t : typ) (e : llvm_exp) : option smt_expr :=
  sym_eval_exp empty_smt_store empty_smt_store (Some t) e
.

Fixpoint fill_smt_store (ls : smt_store) (gs : smt_store) (l : list (raw_id * function_arg)) : option smt_store :=
  match l with
  | (id, ((t, e), _)) :: tail =>
      match (sym_eval_exp ls gs (Some t) e) with
      | Some se =>
          match (fill_smt_store ls gs tail) with
          | Some r => Some (id !-> Some se; r)
          | None => None
          end
      | None => None
      end
  | [] => Some empty_smt_store
  end
.

Definition create_local_smt_store (d : llvm_definition) (ls : smt_store) (gs : smt_store) (args : list function_arg) : option smt_store :=
  match (merge_lists (df_args d) args) with
  | Some l => fill_smt_store ls gs l
  | None => None
  end
.

Fixpoint sym_eval_phi_args ls gs t args pbid : option smt_expr :=
  match args with
  | (bid, e) :: tail =>
      if raw_id_eqb bid pbid then
        sym_eval_exp ls gs (Some t) e
      else
        sym_eval_phi_args ls gs t tail pbid
  | _ => None
  end
.

(* TODO: renmae se/cond/... to ast? *)
Inductive sym_step : sym_state -> sym_state -> Prop :=
  | Sym_Step_OP : forall ic cid v e c cs pbid ls stk gs syms pc mdl se,
      (sym_eval_exp ls gs None e) = Some se ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_Op v e))
          (c :: cs)
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> Some se; ls)
          stk
          gs
          syms
          pc
          mdl
        )
  | Sym_Step_Phi : forall ic cid v t args c cs pbid ls stk gs syms pc mdl se,
      (sym_eval_phi_args ls gs t args pbid) = Some se ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Phi cid (Phi v t args))
          (c :: cs)
          (Some pbid)
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          (next_inst_counter ic c)
          c
          cs
          (Some pbid)
          (v !-> Some se; ls)
          stk
          gs
          syms
          pc
          mdl
        )
  | Sym_Step_UnconditionalBr : forall ic cid tbid pbid ls stk gs syms pc mdl d b c cs,
      (find_function mdl (ic_fid ic)) = Some d ->
      (fetch_block d tbid) = Some b ->
      (blk_cmds b) = c :: cs ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Term cid (TERM_UnconditionalBr tbid))
          []
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          (mk_inst_counter (ic_fid ic) tbid (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          syms
          pc
          mdl
        )
  | Sym_Step_Br_True : forall ic cid e bid1 bid2 pbid ls stk gs syms pc mdl cond d b c cs,
      (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some (Expr Sort_BV1 cond) ->
      (find_function mdl (ic_fid ic)) = Some d ->
      (fetch_block d bid1) = Some b ->
      (blk_cmds b) = c :: cs ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Term cid (TERM_Br ((TYPE_I 1), e) bid1 bid2))
          []
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          (mk_inst_counter (ic_fid ic) bid1 (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          syms
          (AST_BinOp Sort_BV1 SMT_And pc cond)
          mdl
        )
  | Sym_Step_Br_False : forall ic cid e bid1 bid2 pbid ls stk gs syms pc mdl cond d b c cs,
      (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some (Expr Sort_BV1 cond) ->
      (find_function mdl (ic_fid ic)) = Some d ->
      (fetch_block d bid2) = Some b ->
      (blk_cmds b) = c :: cs ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Term cid (TERM_Br ((TYPE_I 1), e) bid1 bid2))
          []
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          (mk_inst_counter (ic_fid ic) bid2 (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          syms
          (AST_BinOp Sort_BV1 SMT_And pc (AST_Not Sort_BV1 cond))
          mdl
        )
  | Sym_Step_VoidCall : forall ic cid f args anns c cs pbid ls stk gs syms pc mdl d b c' cs' ls',
      (find_function_by_exp mdl f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function TYPE_Void (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (create_local_smt_store d ls gs args) = Some ls' ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, f) args anns))
          (c :: cs)
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          None
          ls'
          ((Sym_Frame ls (next_inst_counter ic c) pbid None) :: stk)
          gs
          syms
          pc
          mdl
        )
  | Sym_Step_Call : forall ic cid v t f args anns c cs pbid ls stk gs syms pc mdl d b c' cs' ls',
      (find_function_by_exp mdl f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function t (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (create_local_smt_store d ls gs args) = Some ls' ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_Call v (t, f) args anns))
          (c :: cs)
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          None
          ls'
          ((Sym_Frame ls (next_inst_counter ic c) pbid (Some v)) :: stk)
          gs
          syms
          pc
          mdl
        )
  (* TODO: check the return type of the current function *)
  | Sym_Step_RetVoid : forall ic cid pbid ls ls' ic' pbid' stk gs syms pc mdl d c' cs',
      (find_function mdl (ic_fid ic')) = Some d ->
      (get_trailing_cmds d ic') = Some (c' :: cs') ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Term cid TERM_RetVoid)
          []
          pbid
          ls
          ((Sym_Frame ls' ic' pbid' None) :: stk)
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          ic'
          c'
          cs'
          pbid'
          ls'
          stk
          gs
          syms
          pc
          mdl
        )
  (* TODO: check the return type of the current function *)
  | Sym_Step_Ret : forall ic cid t e pbid ls ls' ic' pbid' v stk gs syms pc mdl se d c' cs',
      (sym_eval_exp ls gs (Some t) e) = Some se ->
      (find_function mdl (ic_fid ic')) = Some d ->
      (get_trailing_cmds d ic') = Some (c' :: cs') ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Term cid (TERM_Ret (t, e)))
          []
          pbid
          ls
          ((Sym_Frame ls' ic' pbid' (Some v)) :: stk)
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          ic'
          c'
          cs'
          pbid'
          (v !-> Some se; ls')
          stk
          gs
          syms
          pc
          mdl
        )
  | Sym_Step_Assume : forall ic cid e attrs c cs pbid ls stk gs syms pc mdl d cond,
      (find_function mdl klee_assume_id) = None ->
      (find_declaration mdl klee_assume_id) = Some d ->
      (dc_type d) = klee_assume_type ->
      (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some (Expr Sort_BV1 cond) ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, klee_assume_exp) [(((TYPE_I 1), e), attrs)] []))
          (c :: cs)
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          ls
          stk
          gs
          syms
          (AST_BinOp Sort_BV1 SMT_And pc cond)
          mdl
        )
  | Sym_Step_MakeSymbolicInt32 : forall ic cid v c cs pbid ls stk gs syms pc mdl d,
      (find_function mdl klee_make_symbolic_int32_id) = None ->
      (find_declaration mdl klee_make_symbolic_int32_id) = Some d ->
      (dc_type d) = klee_make_symbolic_int32_type ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_Call v ((TYPE_I 32), klee_make_symbolic_int32_exp) [] []))
          (c :: cs)
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
        (mk_sym_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> Some (Expr Sort_BV32 (AST_Var Sort_BV32 (fresh_name syms))); ls)
          stk
          gs
          (extend_names syms)
          pc
          mdl
        )
.

Definition multi_sym_step := multi sym_step.

Definition sym_division_error_condition se :=
  match se with
  | Expr sort ast =>
      (AST_CmpOp sort SMT_Eq ast (AST_Const sort (repr_by_sort sort 0)))
  end
.

Definition sym_division_overflow_error_condition se1 se2 :=
  match se1, se2 with
  | Expr Sort_BV32 ast1, Expr Sort_BV32 ast2 =>
      AST_BinOp
        Sort_BV1
        SMT_And
        (AST_CmpOp Sort_BV32 SMT_Eq ast1 (AST_Const Sort_BV32 (repr (-2147483648))))
        (AST_CmpOp Sort_BV32 SMT_Eq ast2 (AST_Const Sort_BV32 (repr (-1))))
  | Expr Sort_BV64 ast1, Expr Sort_BV64 ast2 =>
      AST_BinOp
        Sort_BV1
        SMT_And
        (AST_CmpOp Sort_BV64 SMT_Eq ast1 (AST_Const Sort_BV64 (repr (-9223372036854775808))))
        (AST_CmpOp Sort_BV64 SMT_Eq ast2 (AST_Const Sort_BV64 (repr (-1))))
  | _, _ => smt_ast_false
  end
.

Definition sym_shift_error_condition se :=
  match se with
  | Expr sort ast =>
      AST_CmpOp
        sort
        SMT_Uge
        ast
        (AST_Const sort (repr_by_sort sort (Zpos (smt_sort_to_width sort))))
  end
.

Inductive error_sym_state : sym_state -> Prop :=
  | ESS_Assert : forall ic cid args anns cs pbid ls stk gs syms pc mdl d,
      (find_function mdl assert_id) = None ->
      (find_declaration mdl assert_id) = Some d ->
      (dc_type d) = assert_type ->
      TYPE_Function TYPE_Void (get_arg_types args) false = assert_type ->
      error_sym_state
        (mk_sym_state
          ic
          (CMD_Inst
            cid
            (INSTR_VoidCall (TYPE_Void, assert_exp) args anns)
          )
          cs
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
  | ESS_Unreachable : forall ic cid cs pbid ls stk gs syms pc mdl,
      error_sym_state
        (mk_sym_state
          ic
          (CMD_Term cid TERM_Unreachable)
          cs
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
  | ESS_DivisionByZero : forall ic cid v op t e1 e2 cs pbid ls stk gs syms pc mdl se,
      is_division op ->
      (sym_eval_exp ls gs (Some t) e2) = Some se ->
      sat (AST_BinOp Sort_BV1 SMT_And pc (sym_division_error_condition se)) ->
      error_sym_state
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_Op v (OP_IBinop op t e1 e2)))
          cs
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
  | ESS_DivisionOverflow : forall ic cid v exact t e1 e2 cs pbid ls stk gs syms pc mdl se1 se2,
      (sym_eval_exp ls gs (Some t) e1) = Some se1 ->
      (sym_eval_exp ls gs (Some t) e2) = Some se2 ->
      sat (AST_BinOp Sort_BV1 SMT_And pc (sym_division_overflow_error_condition se1 se2)) ->
      error_sym_state
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_Op v (OP_IBinop (SDiv exact) t e1 e2)))
          cs
          pbid
          ls
          stk
          gs
          syms
          pc
          mdl
        )
  | ESS_OverShift : forall ic cid v op w e1 e2 cs pbid ls stk gs syms pc mdl se,
      is_shift op ->
      (sym_eval_exp ls gs (Some (TYPE_I w)) e2) = Some se ->
      sat (AST_BinOp Sort_BV1 SMT_And pc (sym_shift_error_condition se)) ->
      error_sym_state
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_Op v (OP_IBinop op (TYPE_I w) e1 e2)))
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

Definition init_local_smt_store (m : llvm_module) (d : llvm_definition) : smt_store :=
  empty_smt_store
.

(* TODO: rename to avoid namespace issues *)
Definition get_global_initializer (g : llvm_global) : option smt_expr :=
  match (g_exp g) with
  | Some e => (sym_eval_constant_exp (g_typ g) e)
  | _ => None (* TODO: check against the specifiction *)
  end
.

(* TODO: rename to avoid namespace issues *)
Definition add_global (gs : smt_store) (g : llvm_global) : option smt_store :=
  match (get_global_initializer g) with
  | Some dv => Some ((g_ident g) !-> Some dv; gs)
  | _ => None
  end
.

Fixpoint init_global_smt_store_internal (gs : smt_store) (l : list llvm_global) : option smt_store :=
  match l with
  | g :: tail =>
      match (add_global gs g) with
      | Some gs' => init_global_smt_store_internal gs' tail
      | _ => None
      end
  | [] => Some gs
  end
.

(* TODO: change later? *)
Definition init_global_smt_store (m : llvm_module) : smt_store := empty_smt_store.

Definition init_sym_state (mdl : llvm_module) (fid : function_id) : option sym_state :=
  match (find_function mdl fid) with
  | Some d =>
    match (build_inst_counter mdl d) with
    | Some ic =>
        match (entry_block d) with
        | Some b =>
            match (blk_cmds b) with
            | cmd :: tail =>
                Some (mk_sym_state
                  ic
                  cmd
                  tail
                  None
                  (init_local_smt_store mdl d)
                  []
                  (init_global_smt_store mdl)
                  []
                  smt_ast_true
                  mdl
                )
            | _ => None
            end
        | None => None
        end
    | None => None
    end
  | None => None
  end
.

(* TODO: move from here? *)
Definition get_sort_by_dynamic_int (x : dynamic_int) : smt_sort :=
  match x with
  | DI_I1 n => Sort_BV1
  | DI_I8 n => Sort_BV8
  | DI_I16 n => Sort_BV16
  | DI_I24 n => Sort_BV24
  | DI_I32 n => Sort_BV32
  | DI_I40 n => Sort_BV40
  | DI_I48 n => Sort_BV48
  | DI_I56 n => Sort_BV56
  | DI_I64 n => Sort_BV64
  end
.

Definition make_dynamic_int (s : smt_sort) (x : smt_sort_to_int_type s) : dynamic_int :=
  let f :=
    match s return smt_sort_to_int_type s -> dynamic_int with
    | Sort_BV1 => DI_I1
    | Sort_BV8 => DI_I8
    | Sort_BV16 => DI_I16
    | Sort_BV24 => DI_I24
    | Sort_BV32 => DI_I32
    | Sort_BV40 => DI_I40
    | Sort_BV48 => DI_I48
    | Sort_BV56 => DI_I56
    | Sort_BV64 => DI_I64
    end
  in f x
.

Inductive over_approx_via_model :
  option dynamic_value -> option smt_expr -> smt_model -> Prop :=
  | OA_None : forall m,
      over_approx_via_model None None m
  | OA_Some : forall m sort (ast : smt_ast sort) (i : smt_sort_to_int_type sort) di,
      (smt_eval_ast m sort ast) = i ->
      (make_dynamic_int sort i) = di ->
      over_approx_via_model (Some (DV_Int di)) (Some (Expr sort ast)) m
.

Inductive over_approx_store_via : smt_store -> dv_store -> smt_model -> Prop :=
  | OA_Store : forall c_s s_s m,
      (forall (x : raw_id), over_approx_via_model (c_s x) (s_s x) m) ->
      over_approx_store_via s_s c_s m
.

Inductive over_approx_frame_via : sym_frame -> frame -> smt_model -> Prop :=
  | OA_Frame : forall s_s c_s m ic pbid v,
      over_approx_store_via s_s c_s m ->
      over_approx_frame_via
        (Sym_Frame s_s ic pbid v)
        (Frame c_s ic pbid v)
        m
.

Inductive over_approx_stack_via : list sym_frame -> list frame -> smt_model -> Prop :=
  | OA_Stack_Empty : forall m,
      over_approx_stack_via [] [] m
  | OA_Stack_NonEmpty : forall s_f s_stk c_f c_stk m,
      over_approx_frame_via s_f c_f m ->
      over_approx_stack_via s_stk c_stk m ->
      over_approx_stack_via (s_f :: s_stk) (c_f :: c_stk) m
.

Inductive over_approx_via : sym_state -> state -> smt_model -> Prop :=
  | OAV_State : forall ic c cs pbid s_ls s_stk s_gs syms pc mdl c_ls c_stk c_gs m,
      (over_approx_store_via s_ls c_ls m) ->
      (over_approx_stack_via s_stk c_stk m) ->
      (over_approx_store_via s_gs c_gs m) ->
      ((smt_eval_ast m Sort_BV1 pc) = one) ->
      over_approx_via
        (mk_sym_state
          ic
          c
          cs
          pbid
          s_ls
          s_stk
          s_gs
          syms
          pc
          mdl
        )
        (mk_state
          ic
          c
          cs
          pbid
          c_ls
          c_stk
          c_gs
          mdl
        )
        m
.

Inductive over_approx : sym_state -> state -> Prop :=
  | OA_State : forall s c,
      (exists m, over_approx_via s c m) -> over_approx s c
.

Lemma pc_unsat_lemma : forall s s',
  sym_step s s' -> unsat_sym_state s -> unsat_sym_state s'.
Proof.
  intros s s' Hss Hu.
  inversion Hss; try (
    apply Unsat_State;
    subst;
    inversion Hu; subst;
    assumption
  ); try (
    apply Unsat_State;
    subst;
    inversion Hu; subst;
    apply unsat_and_left;
    assumption
  ).
Qed.
