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
From SE.Utils Require Import Util.

(* TODO: smt_store -> sym_store? *)

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
  sym_pc : smt_expr;
  sym_module : llvm_module;
}.

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
        if (w2 =? w1)%positive then
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
        if (w2 =? w1)%positive then
          Some e
        else
          if (w2 <=? w1)%positive then
            Some (SMT_Extract e 0 w2)
          else
            Some (SMT_SExt e w2)
    | _, _ => None
    end
  | Bitcast => Some e
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
  | EXP_Bool b => Some (make_smt_bool b)
  | EXP_Null => None
  | EXP_Zero_initializer => None
  | EXP_Undef => None (* TODO: how to handle? *)
  | EXP_Poison => None
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
  | OP_Conversion conv t1 v t2 =>
      match sym_eval_exp s g (Some t1) v with
      | Some e => sym_convert conv e t1 t2
      | _ => None
      end
  | OP_Select _ _ _ => None
  end
.

Definition sym_eval_constant_exp (t : typ) (e : exp typ) : option smt_expr :=
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
  | Sym_Step_Br_True : forall ic cid e bid1 bid2 pbid ls stk gs syms pc mdl se d b c cs,
      (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some se ->
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
          (SMT_BinOp SMT_And pc se)
          mdl
        )
  | Sym_Step_Br_False : forall ic cid e bid1 bid2 pbid ls stk gs syms pc mdl se d b c cs,
      (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some se ->
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
          (SMT_BinOp SMT_And pc (SMT_Not se)) (* TODO: SMT_Not? *)
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
  | Sym_Step_Assume : forall ic cid e attrs c cs pbid ls stk gs syms pc mdl d se,
      (find_function mdl klee_assume_id) = None ->
      (find_declaration mdl klee_assume_id) = Some d ->
      (dc_type d) = klee_assume_type ->
      (sym_eval_exp ls gs (Some (TYPE_I 1)) e) = Some se ->
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
          (SMT_BinOp SMT_And pc se)
          mdl
        )
  | Sym_Step_MakeSymbolicInt32 : forall ic cid v c cs pbid ls stk gs syms pc mdl d name,
      (find_function mdl klee_make_symbolic_int32_id) = None ->
      (find_declaration mdl klee_make_symbolic_int32_id) = Some d ->
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
          mdl
        )
        (mk_sym_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> Some (SMT_Var_I32 name); ls)
          stk
          gs
          (name :: syms)
          pc
          mdl
        )
.

Definition multi_sym_step := multi sym_step.

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
                  SMT_True
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

(* TODO: rename (corresponds/over_approx) *)
Inductive equiv_via_model : option dynamic_value -> option smt_expr -> smt_model -> Prop :=
  | EVM_None : forall m, equiv_via_model None None m
  | EVM_NoneViaModel : forall m se,
      (smt_eval m se) = None -> equiv_via_model None (Some se) m
  | EVM_Some : forall m di se,
      (smt_eval m se) = Some di -> equiv_via_model (Some (DV_Int di)) (Some se) m
.

(* TODO: use in the relevant locations *)
Inductive over_approx_store_via : smt_store -> dv_store -> smt_model -> Prop :=
  | OA_Store : forall c_s s_s m,
      (forall (x : raw_id), equiv_via_model (c_s x) (s_s x) m) ->
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
  | OA_State : forall s c,
      (exists m, over_approx_via s c m) -> over_approx s c
.

Lemma error_correspondence: forall c s,
  over_approx s c -> (error_sym_state s <-> error_state c).
Proof.
  intros c s Hoa.
  split; (inversion Hoa; destruct H as [m H]; inversion H; subst; intros He).
  {
    inversion He; subst.
    apply ES_Assert with (d := d); assumption.
  }
  {
    inversion He; subst.
    apply ESS_Assert with (d := d); assumption.
  }
Qed.

(* needed for soundness? *)
Lemma pc_sat_lemma : forall s s' m,
  sym_step s s' -> sat_sym_state m s' -> sat_sym_state m s.
Proof.
Admitted.

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
    apply unsat_and;
    assumption
  ).
Qed.
