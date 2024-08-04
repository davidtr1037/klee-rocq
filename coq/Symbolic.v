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
From SE Require Import Relation.

From SE.SMT Require Import Expr.
From SE.SMT Require Import Model.

(* TODO: smt_store -> sym_store? *)

Definition smt_store := total_map smt_expr.

Definition empty_smt_store := empty_map (SMT_Const_I1 zero).

Definition global_smt_store := smt_store.

Inductive sym_frame : Type :=
  | Sym_Frame (s : smt_store) (ic : inst_counter) (pbid : option block_id) (v : raw_id)
  | Sym_Frame_NoReturn (s : smt_store) (ic : inst_counter) (pbid : option block_id)
.

(* TODO: define as an inductive type? *)
Record sym_state : Type := mk_sym_state {
  sym_ic : inst_counter;
  sym_cmd : llvm_cmd;
  sym_block : list llvm_cmd;
  sym_prev_bid : option block_id;
  sym_store : smt_store;
  sym_stack : list sym_frame;
  sym_globals : global_smt_store;
  sym_symbolics : list string;
  sym_pc : smt_expr;
  sym_module : llvm_module;
}.

(* TODO: define error_sym_state *)

(* TODO: ... *)
Definition build_local_smt_store (m : llvm_module) (d : llvm_definition) : smt_store :=
  empty_smt_store
.

Definition build_global_smt_store (m : llvm_module) : option global_smt_store := None.

Definition init_sym_state (m : llvm_module) (d : llvm_definition) : option sym_state :=
  match (build_global_smt_store m) with
  | Some gs =>
    match (build_inst_counter m d) with
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
                  (build_local_smt_store m d)
                  []
                  gs
                  []
                  SMT_True
                  m
                )
            | _ => None
            end
        | None => None
        end
    | None => None
    end
  | _ => None
  end
.

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

Definition sym_lookup_ident (s : smt_store) (g : global_smt_store) (id : ident) : smt_expr :=
  match id with
  | ID_Local x => s x
  | ID_Global x => g x
  end
.

Definition sym_eval_ibinop (op : ibinop) (e1 e2 : smt_expr) : smt_expr :=  
  match op with
  (* TODO: how to handle the flags? *)
  | Add nuw nsw => SMT_BinOp SMT_Add e1 e2
  | Sub nuw nsw => SMT_BinOp SMT_Sub e1 e2
  | Mul nuw nsw => SMT_BinOp SMT_Mul e1 e2
  | Shl nuw nsw => SMT_BinOp SMT_Shl e1 e2
  | UDiv exact => SMT_BinOp SMT_UDiv e1 e2
  | SDiv exact => SMT_BinOp SMT_SDiv e1 e2
  | LShr exact => SMT_BinOp SMT_LShr e1 e2
  | AShr exact => SMT_BinOp SMT_AShr e1 e2
  | URem => SMT_BinOp SMT_URem e1 e2
  | SRem => SMT_BinOp SMT_SRem e1 e2
  | And => SMT_BinOp SMT_And e1 e2
  | Or => SMT_BinOp SMT_Or e1 e2
  | Xor => SMT_BinOp SMT_Xor e1 e2
  end
.

Definition sym_eval_icmp (op : icmp) (e1 e2 : smt_expr) : smt_expr :=
  match op with
  | Eq => SMT_CmpOp SMT_Eq e1 e2
  | Ne => SMT_CmpOp SMT_Ne e1 e2
  | Ugt => SMT_CmpOp SMT_Uge e1 e2
  | Uge => SMT_CmpOp SMT_Uge e1 e2
  | Ult => SMT_CmpOp SMT_Ult e1 e2
  | Ule => SMT_CmpOp SMT_Ule e1 e2
  | Sgt => SMT_CmpOp SMT_Sgt e1 e2
  | Sge => SMT_CmpOp SMT_Sge e1 e2
  | Slt => SMT_CmpOp SMT_Slt e1 e2
  | Sle => SMT_CmpOp SMT_Sle e1 e2
  end
.

Definition sym_convert (conv : conversion_type) (e : smt_expr) t1 t2 : option smt_expr :=
  match conv with
  | Trunc =>
    match t1, t2 with
    | TYPE_I w1, TYPE_I w2 =>
        if (w2 <=? w1)%positive then
          Some (SMT_Extract e 0 w2)
        else
          None
    | _, _ => None
    end
  | Zext =>
    match t1, t2 with
    | TYPE_I w1, TYPE_I w2 =>
        if (w1 =? w2)%positive then
          Some e
        else
          if (w2 <=? w1)%positive then
            Some (SMT_Extract e 0 w2)
          else
            Some (SMT_ZExt e w2)
    | _, _ => None
    end
  | Sext =>
    match t1, t2 with
    | TYPE_I w1, TYPE_I w2 =>
        if (w1 =? w2)%positive then
          Some e
        else
          if (w2 <=? w1)%positive then
            Some (SMT_Extract e 0 w2)
          else
            Some (SMT_SExt e w2)
    | _, _ => None
    end
  | Bitcast => Some e
  | Uitofp
  | Sitofp
  | Fptoui
  | Fptosi
  | Fptrunc
  | Fpext
  | Inttoptr
  | Ptrtoint
  | Addrspacecast => None
  end
.

Fixpoint sym_eval_exp (s : smt_store) (g : global_smt_store) (t : option typ) (e : exp typ) : option smt_expr :=
  match e with
  | EXP_Ident id => Some (sym_lookup_ident s g id)
  | EXP_Integer n =>
      match t with
      | Some (TYPE_I bits) => make_smt_const bits n
      | _ => None
      end
  | EXP_Float f => None
  | EXP_Double f => None
  | EXP_Hex f => None
  | EXP_Bool b => Some (make_smt_bool b)
  | EXP_Null => None
  | EXP_Zero_initializer => None
  | EXP_Cstring elts => None
  | EXP_Undef => None (* TODO: how to handle? *)
  | EXP_Poison => None
  | EXP_Struct fields => None
  | EXP_Packed_struct fields => None
  | EXP_Array elts => None
  | EXP_Vector elts => None
  | OP_IBinop iop t v1 v2 =>
      match (sym_eval_exp s g (Some t) v1, sym_eval_exp s g (Some t) v2) with
      | (Some e1, Some e2) => Some (sym_eval_ibinop iop e1 e2)
      | (_, _) => None
      end
  | OP_ICmp icmp t v1 v2 =>
      match (sym_eval_exp s g (Some t) v1, sym_eval_exp s g (Some t) v2) with
      | (Some e1, Some e2) => Some (sym_eval_icmp icmp e1 e2)
      | (_, _) => None
      end
  | OP_FBinop fop _ _ _ _ => None
  | OP_FCmp _ _ _ _ => None
  | OP_Conversion conv t1 v t2 =>
      match sym_eval_exp s g (Some t1) v with
      | Some e => sym_convert conv e t1 t2
      | _ => None
      end
  | OP_GetElementPtr _ _ _ => None
  | OP_ExtractElement _ _ => None
  | OP_InsertElement _ _ _ => None
  | OP_ShuffleVector _ _ _ => None
  | OP_ExtractValue _ _ => None
  | OP_InsertValue _ _ _ => None
  | OP_Select _ _ _ => None
  | OP_Freeze _ => None
  end
.

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
          (v !-> se; ls)
          stk
          gs
          syms
          pc
          mdl
        )
.
(*
  | Step_Phi : forall ic cid v t args c cs pbid ls stk gs m dv,
      (eval_phi_args ls gs t args pbid) = Some dv ->
      step
        (mk_state
          ic
          (CMD_Phi cid (Phi v t args))
          (c :: cs)
          (Some pbid)
          ls
          stk
          gs
          m
        )
        (mk_state
          (next_inst_counter ic c)
          c
          cs
          (Some pbid)
          (v !-> dv; ls)
          stk
          gs
          m
        )
  | Step_UnconditionalBr : forall ic cid tbid pbid ls stk gs m d b c cs,
      (find_function m (fid ic)) = Some d ->
      (fetch_block d tbid) = Some b ->
      (blk_cmds b) = c :: cs ->
      step
        (mk_state
          ic
          (CMD_Term cid (TERM_UnconditionalBr tbid))
          []
          pbid
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (fid ic) tbid (get_cmd_id c))
          c
          cs
          (Some (bid ic))
          ls
          stk
          gs
          m
        )
  | Step_Br_True : forall ic cid t e bid1 bid2 pbid ls stk gs m d b c cs,
      (eval_exp ls gs (Some t) e) = Some dv_true ->
      (find_function m (fid ic)) = Some d ->
      (fetch_block d bid1) = Some b ->
      (blk_cmds b) = c :: cs ->
      step
        (mk_state
          ic
          (CMD_Term cid (TERM_Br (t, e) bid1 bid2))
          []
          pbid
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (fid ic) bid1 (get_cmd_id c))
          c
          cs
          (Some (bid ic))
          ls
          stk
          gs
          m
        )
  | Step_Br_False : forall ic cid t e bid1 bid2 pbid ls stk gs m d b c cs,
      (eval_exp ls gs (Some t) e) = Some dv_true ->
      (find_function m (fid ic)) = Some d ->
      (fetch_block d bid2) = Some b ->
      (blk_cmds b) = c :: cs ->
      step
        (mk_state
          ic
          (CMD_Term cid (TERM_Br (t, e) bid1 bid2))
          []
          pbid
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (fid ic) bid2 (get_cmd_id c))
          c
          cs
          (Some (bid ic))
          ls
          stk
          gs
          m
        )
  | Step_VoidCall : forall ic cid f args anns c cs pbid ls stk gs m d b c' cs' dvs ls',
      (find_function_by_exp m f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function TYPE_Void (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (eval_args ls gs args) = Some dvs ->
      (init_local_store d  dvs) = Some ls' ->
      step
        (mk_state
          ic
          (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, f) args anns))
          (c :: cs)
          pbid
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          None
          ls'
          ((Frame_NoReturn ls (next_inst_counter ic c) pbid) :: stk)
          gs
          m
        )
  | Step_Call : forall ic cid v t f args anns c cs pbid ls stk gs m d b c' cs' dvs ls',
      (find_function_by_exp m f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function t (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (eval_args ls gs args) = Some dvs ->
      (init_local_store d dvs) = Some ls' ->
      step
        (mk_state
          ic
          (CMD_Inst cid (INSTR_Call v (t, f) args anns))
          (c :: cs)
          pbid
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          None
          ls'
          ((Frame ls (next_inst_counter ic c) None v) :: stk)
          gs
          m
        )
  (* TODO: check the return type of the current function *)
  | Step_RetVoid : forall ic cid pbid ls ls' ic' pbid' stk gs m d c' cs',
      (find_function m (fid ic')) = Some d ->
      (get_trailing_cmds d ic') = Some (c' :: cs') ->
      step
        (mk_state
          ic
          (CMD_Term cid TERM_RetVoid)
          []
          pbid
          ls
          ((Frame_NoReturn ls' ic' pbid') :: stk)
          gs
          m
        )
        (mk_state
          ic'
          c'
          cs'
          pbid'
          ls'
          stk
          gs
          m
        )
  (* TODO: check the return type of the current function *)
  | Step_Ret : forall ic cid t e pbid ls ls' ic' pbid' v stk gs m dv d c' cs',
      (eval_exp ls gs (Some t) e) = Some dv ->
      (find_function m (fid ic')) = Some d ->
      (get_trailing_cmds d ic') = Some (c' :: cs') ->
      step
        (mk_state
          ic
          (CMD_Term cid (TERM_Ret (t, e)))
          []
          pbid
          ls
          ((Frame ls' ic' pbid' v) :: stk)
          gs
          m
        )
        (mk_state
          ic'
          c'
          cs'
          pbid'
          (v !-> dv; ls')
          stk
          gs
          m
        )
  | Step_MakeSymbolicInt32 : forall ic cid v c cs pbid ls stk gs m n d,
      (find_function m klee_make_symbolic_int32_id) = None ->
      (find_declaration m klee_make_symbolic_int32_id) = Some d ->
      (dc_type d) = klee_make_symbolic_int32_type ->
      step
        (mk_state
          ic
          (CMD_Inst cid (INSTR_Call v ((TYPE_I 32), klee_make_symbolic_int32_exp) [] []))
          (c :: cs)
          pbid
          ls
          stk
          gs
          m
        )
        (mk_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> (DV_Int (DI_I32 (repr n))); ls)
          stk
          gs
          m
        )
  (* TODO: what is the expected type of the argument (t)? *)
  | Step_Assume : forall ic cid t e attrs c cs pbid ls stk gs m d dv,
      (find_function m klee_assume_id) = None ->
      (find_declaration m klee_assume_id) = Some d ->
      (dc_type d) = klee_assume_type ->
      (eval_exp ls gs (Some t) e) = Some dv ->
      (* TODO: verify this... *)
      (convert Trunc dv t (TYPE_I 1)) = Some dv_true ->
      step
        (mk_state
          ic
          (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, klee_assume_exp) [((t, e), attrs)] []))
          (c :: cs)
          pbid
          ls
          stk
          gs
          m
        )
        (mk_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          ls
          stk
          gs
          m
        )
.
*)
