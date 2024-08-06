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

From SE.Utils Require Import ListUtil.

(* TODO: smt_store -> sym_store? *)

Definition smt_store := total_map (option smt_expr).

Definition empty_smt_store := empty_map (Some (SMT_Const_I1 zero)).

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
  sym_globals : smt_store;
  sym_symbolics : list string;
  sym_pc : smt_expr;
  sym_module : llvm_module;
}.

Inductive error_sym_state : sym_state -> Prop :=
  | ES_Assert : forall ic cid args anns cs pbid ls stk gs syms pc m d,
      (find_function m assert_id) = None ->
      (find_declaration m assert_id) = Some d ->
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
          m
       )
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

Definition sym_lookup_ident (s : smt_store) (g : smt_store) (id : ident) : option smt_expr :=
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

Fixpoint sym_eval_exp (s : smt_store) (g : smt_store) (t : option typ) (e : exp typ) : option smt_expr :=
  match e with
  | EXP_Ident id => sym_lookup_ident s g id
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
  | OP_IBinop op t v1 v2 =>
      match (sym_eval_exp s g (Some t) v1, sym_eval_exp s g (Some t) v2) with
      | (Some e1, Some e2) => Some (sym_eval_ibinop op e1 e2)
      | (_, _) => None
      end
  | OP_ICmp op t v1 v2 =>
      match (sym_eval_exp s g (Some t) v1, sym_eval_exp s g (Some t) v2) with
      | (Some e1, Some e2) => Some (sym_eval_icmp op e1 e2)
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

Fixpoint sym_eval_constant_exp (t : typ) (e : exp typ) : option smt_expr :=
  sym_eval_exp empty_smt_store empty_smt_store (Some t) e
.

Definition sym_eval_arg (ls : smt_store) (gs : smt_store) (arg : function_arg) : option smt_expr :=
  match arg with
  | ((t, e), _) => sym_eval_exp ls gs (Some t) e
  end
.

Fixpoint sym_eval_args (ls : smt_store) (gs : smt_store) (args : list function_arg) : option (list smt_expr) :=
  match args with
  | arg :: tail =>
      match (sym_eval_arg ls gs arg) with
      | Some e =>
          match (sym_eval_args ls gs tail) with
          | Some es => Some (e :: es)
          | _ => None
          end
      | _ => None
      end
  | _ => Some []
  end
.

Fixpoint fill_smt_store (l : list (raw_id * smt_expr)) : smt_store :=
  match l with
  | (id, e) :: tail => (id !-> Some e; (fill_smt_store tail))
  | [] => empty_smt_store
  end
.

Definition create_local_smt_store (d : llvm_definition) (es : list smt_expr) : option smt_store :=
  match (merge_lists (df_args d) es) with
  | Some l => Some (fill_smt_store l)
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
  | Sym_Step_Phi : forall ic cid v t args c cs pbid ls stk gs syms pc m se,
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
          m
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
          m
        )
  | Sym_Step_UnconditionalBr : forall ic cid tbid pbid ls stk gs syms pc m d b c cs,
      (find_function m (fid ic)) = Some d ->
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
          m
        )
        (mk_sym_state
          (mk_inst_counter (fid ic) tbid (get_cmd_id c))
          c
          cs
          (Some (bid ic))
          ls
          stk
          gs
          syms
          pc
          m
        )
  (* TODO: t must by i1? *)
  | Sym_Step_Br_True : forall ic cid t e bid1 bid2 pbid ls stk gs syms pc m se d b c cs,
      (sym_eval_exp ls gs (Some t) e) = Some se ->
      (find_function m (fid ic)) = Some d ->
      (fetch_block d bid1) = Some b ->
      (blk_cmds b) = c :: cs ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Term cid (TERM_Br (t, e) bid1 bid2))
          []
          pbid
          ls
          stk
          gs
          syms
          pc
          m
        )
        (mk_sym_state
          (mk_inst_counter (fid ic) bid1 (get_cmd_id c))
          c
          cs
          (Some (bid ic))
          ls
          stk
          gs
          syms
          (SMT_BinOp SMT_And pc se)
          m
        )
  (* TODO: t must by i1? *)
  | Sym_Step_Br_False : forall ic cid t e bid1 bid2 pbid ls stk gs syms pc m se d b c cs,
      (sym_eval_exp ls gs (Some t) e) = Some se ->
      (find_function m (fid ic)) = Some d ->
      (fetch_block d bid2) = Some b ->
      (blk_cmds b) = c :: cs ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Term cid (TERM_Br (t, e) bid1 bid2))
          []
          pbid
          ls
          stk
          gs
          syms
          pc
          m
        )
        (mk_sym_state
          (mk_inst_counter (fid ic) bid2 (get_cmd_id c))
          c
          cs
          (Some (bid ic))
          ls
          stk
          gs
          syms
          (SMT_BinOp SMT_And pc (SMT_Not se)) (* TODO: SMT_Not? *)
          m
        )
  | Sym_Step_VoidCall : forall ic cid f args anns c cs pbid ls stk gs syms pc m d b c' cs' es ls',
      (find_function_by_exp m f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function TYPE_Void (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (sym_eval_args ls gs args) = Some es ->
      (create_local_smt_store d es) = Some ls' ->
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
          m
        )
        (mk_sym_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          None
          ls'
          ((Sym_Frame_NoReturn ls (next_inst_counter ic c) pbid) :: stk)
          gs
          syms
          pc
          m
        )
  | Sym_Step_Call : forall ic cid v t f args anns c cs pbid ls stk gs syms pc m d b c' cs' es ls',
      (find_function_by_exp m f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function t (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (sym_eval_args ls gs args) = Some es ->
      (create_local_smt_store d es) = Some ls' ->
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
          m
        )
        (mk_sym_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          None
          ls'
          ((Sym_Frame ls (next_inst_counter ic c) pbid v) :: stk)
          gs
          syms
          pc
          m
        )
  (* TODO: check the return type of the current function *)
  | Sym_Step_RetVoid : forall ic cid pbid ls ls' ic' pbid' stk gs syms pc m d c' cs',
      (find_function m (fid ic')) = Some d ->
      (get_trailing_cmds d ic') = Some (c' :: cs') ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Term cid TERM_RetVoid)
          []
          pbid
          ls
          ((Sym_Frame_NoReturn ls' ic' pbid') :: stk)
          gs
          syms
          pc
          m
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
          m
        )
  (* TODO: check the return type of the current function *)
  | Sym_Step_Ret : forall ic cid t e pbid ls ls' ic' pbid' v stk gs syms pc m se d c' cs',
      (sym_eval_exp ls gs (Some t) e) = Some se ->
      (find_function m (fid ic')) = Some d ->
      (get_trailing_cmds d ic') = Some (c' :: cs') ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Term cid (TERM_Ret (t, e)))
          []
          pbid
          ls
          ((Sym_Frame ls' ic' pbid' v) :: stk)
          gs
          syms
          pc
          m
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
          m
        )
  (* TODO: what is the expected type of the argument (t)? *)
  | Sym_Step_Assume : forall ic cid t e attrs c cs pbid ls stk gs syms pc m d se cond,
      (find_function m klee_assume_id) = None ->
      (find_declaration m klee_assume_id) = Some d ->
      (dc_type d) = klee_assume_type ->
      (sym_eval_exp ls gs (Some t) e) = Some se ->
      (sym_convert Trunc se t (TYPE_I 1)) = Some cond ->
      sym_step
        (mk_sym_state
          ic
          (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, klee_assume_exp) [((t, e), attrs)] []))
          (c :: cs)
          pbid
          ls
          stk
          gs
          syms
          pc
          m
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
          (SMT_BinOp SMT_And pc cond)
          m
        )
  | Sym_Step_MakeSymbolicInt32 : forall ic cid v c cs pbid ls stk gs syms pc m d name,
      (find_function m klee_make_symbolic_int32_id) = None ->
      (find_declaration m klee_make_symbolic_int32_id) = Some d ->
      (dc_type d) = klee_make_symbolic_int32_type ->
      (~ In name syms) ->
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
          m
        )
        (mk_sym_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> Some (SMT_Var name); ls)
          stk
          gs
          (name :: syms)
          pc
          m
        )
.

Definition multi_sym_step := multi sym_step.

Definition init_local_smt_store (m : llvm_module) (d : llvm_definition) : smt_store :=
  empty_smt_store
.

Definition get_global_initializer (g : llvm_global) : option smt_expr :=
  match (g_exp g) with
  | Some e => (sym_eval_constant_exp (g_typ g) e)
  | _ => None (* TODO: check against the specifiction *)
  end
.

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

Definition init_global_smt_store (m : llvm_module) : option smt_store :=
  init_global_smt_store_internal empty_smt_store (m_globals m)
.

Definition init_sym_state (m : llvm_module) (d : llvm_definition) : option sym_state :=
  match (init_global_smt_store m) with
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
                  (init_local_smt_store m d)
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

Inductive over_approx_via : sym_state -> state -> smt_model -> Prop :=
  | OAV_State :
      forall ic c cs pbid s_ls s_stk s_gs syms pc mdl c_ls c_stk c_gs m,
      (forall (x : raw_id), exists di e,
        (c_ls x) = Some (DV_Int di) /\
        (s_ls x) = Some e /\
        (smt_eval m e) = Some di
      ) /\
      (forall (x : raw_id), exists di e,
        (c_gs x) = Some (DV_Int di) /\
        (s_gs x) = Some e /\
        (smt_eval m e) = Some di
      ) /\
      ((smt_eval m pc) = Some di_true) ->
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
  | OA_State :
      forall s c, (exists m, over_approx_via s c m) -> over_approx s c
.

Inductive well_defined_smt_store : smt_store -> list string -> Prop :=
  | WD_SMTStore : forall s syms,
      (forall x n, exists e, (s x) = Some e -> subexpr (SMT_Var n) e -> In n syms) ->
      well_defined_smt_store s syms
.

Inductive well_defined : sym_state -> Prop :=
  | WD_State : forall ic c cs pbid ls stk gs syms pc mdl,
      (well_defined_smt_store ls syms /\ well_defined_smt_store gs syms /\ (forall n, subexpr (SMT_Var n) pc -> In n syms)) ->
      well_defined
        (mk_sym_state
          ic
          c
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

Lemma well_defined_init_sym_state :
  forall mdl d, exists s, (init_sym_state mdl d) = Some s -> well_defined s.
Proof.
Admitted.

Lemma well_defined_sym_eval : forall (s : sym_state) (t : option typ) (e : exp typ),
  (well_defined s) ->
  (forall n, exists se,
    (sym_eval_exp (sym_store s) (sym_globals s) t e) = Some se ->
    subexpr (SMT_Var n) se ->
    In n (sym_symbolics s)
  )
.
Proof.
Admitted.

Lemma well_defined_sym_step : forall (s s' : sym_state),
  well_defined s -> sym_step s s' -> well_defined s'
.
Proof.
Admitted.

Lemma error_correspondence: forall c s,
  over_approx s c -> (error_sym_state s <-> error_state c).
Proof.
Admitted.

Lemma pc_sat_lemma : forall s s' m,
  sym_step s s' -> sat_sym_state m s' -> sat_sym_state m s.
Proof.
Admitted.

Lemma pc_unsat_lemma : forall s s',
  sym_step s s' -> unsat_sym_state s -> unsat_sym_state s'.
Proof.
Admitted.

Lemma soundness_single_step :
  forall s s' c m,
    sym_step s s' ->
    over_approx_via s c m ->
    sat_sym_state m s' ->
    (exists c', step c c' /\ over_approx_via s' c' m).
Proof.
Admitted.

Lemma soundness :
  forall (mdl : llvm_module) (d : llvm_definition) (s : sym_state) (m : smt_model),
    exists init_s,
      (init_sym_state mdl d) = Some init_s ->
      multi_sym_step init_s s ->
      sat_sym_state m s ->
      (exists init_c c, (init_state mdl d) = Some init_c /\ (multi_step c c) /\ over_approx_via s c m).
Proof.
Admitted.

Lemma completeness_single_step :
  forall c c' s,
    step c c' -> well_defined s -> over_approx s c -> (exists s', sym_step s s' /\ over_approx s' c').
Proof.
Admitted.

Lemma completeness :
  forall (mdl : llvm_module) (d : llvm_definition) (c : state),
    exists init_c,
      (init_state mdl d) = Some init_c ->
      multi_step init_c c ->
      (exists init_s s, (init_sym_state mdl d) = Some init_s /\ multi_sym_step init_s s /\ over_approx s c).
Proof.
Admitted.
