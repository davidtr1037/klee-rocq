From Coq Require Import List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import DynamicValue.
From SE Require Import LLVMAst.
From SE Require Import LLVMUtils.
From SE Require Import Relation.

From SE.Numeric Require Import Integers.

From SE.Utils Require Import IDMap.
From SE.Utils Require Import ListUtil.

Record inst_counter := mk_inst_counter {
  ic_fid : function_id;
  ic_bid : block_id;
  ic_cid : cmd_id;
}.

Definition dv_store := total_map (option dynamic_value).

Definition empty_dv_store : dv_store := empty_map None.

Inductive frame : Type :=
  | Frame (s : dv_store) (ic : inst_counter) (pbid : option block_id) (v : option raw_id)
.

(* TODO: define as an inductive type? *)
Record state : Type := mk_state {
  ic : inst_counter;
  cmd : llvm_cmd;
  block : list llvm_cmd;
  prev_bid : option block_id; (* TODO: add to inst_counter? *)
  store : dv_store; (* TODO: rename *)
  stack : list frame;
  globals : dv_store;
  module : llvm_module;
}.

Definition assert_id := (Name "__assert_fail").
Definition assert_exp : llvm_exp := (EXP_Ident (ID_Global assert_id)).
Definition assert_type :=
  TYPE_Function
    TYPE_Void
    [
      (TYPE_Pointer (TYPE_I 8));
      (TYPE_Pointer (TYPE_I 8));
      (TYPE_I 32);
      (TYPE_Pointer (TYPE_I 8))
    ]
    false
.

(* TODO: move to LLVMAst/CFG? *)
Fixpoint get_arg_types (args : list (function_arg)) : list typ :=
  match args with
  | ((t, e), _) :: tail => t :: get_arg_types tail
  | [] => []
  end
.

Definition lookup_ident (s : dv_store) (g : dv_store) (id : ident) : option dynamic_value :=
  match id with
  | ID_Local x => s x
  | ID_Global x => g x
  end
.

Definition eval_ident (s : dv_store) (g : dv_store) (ot : option typ) (id : ident) : option dynamic_value :=
  match ot with
  | Some t =>
    match (lookup_ident s g id) with
    | Some dv =>
        match t, dv with
        | TYPE_I 1, DV_Int (DI_I1 n) => Some dv
        | TYPE_I 8, DV_Int (DI_I8 n) => Some dv
        | TYPE_I 16, DV_Int (DI_I16 n) => Some dv
        | TYPE_I 32, DV_Int (DI_I32 n) => Some dv
        | TYPE_I 64, DV_Int (DI_I64 n) => Some dv
        | _, _ => None
        end
    | None => None
    end
  | None => lookup_ident s g id
  end
.

Definition eval_select cond dv1 dv2 : option dynamic_value :=
  match cond with
  | DV_Int (DI_I1 n) =>
      match dv1, dv2 with
      | DV_Int (DI_I1 n1),  DV_Int (DI_I1 n2)
      | DV_Int (DI_I8 n1),  DV_Int (DI_I8 n2)
      | DV_Int (DI_I16 n1), DV_Int (DI_I16 n2)
      | DV_Int (DI_I32 n1), DV_Int (DI_I32 n2)
      | DV_Int (DI_I64 n1), DV_Int (DI_I64 n2) =>
          if eq n one then Some dv1 else Some dv2
      | DV_Poison _, _
      | _, DV_Poison _ =>
          if eq n one then Some dv1 else Some dv2
      | _, _ => None
      end
  | _ => None
  end
.

(* TODO: why vellvm passes dtyp? *)
Fixpoint eval_exp (s : dv_store) (g : dv_store) (t : option typ) (e : llvm_exp) : option dynamic_value :=
  match e with
  | EXP_Ident id => eval_ident s g t id
  | EXP_Integer n =>
      match t with
      | Some (TYPE_I bits) => make_dv bits n
      | _ => None
      end
  | EXP_Bool b => Some (make_bool b)
  | EXP_Null => None
  | EXP_Zero_initializer => None
  | EXP_Undef =>
      match t with
      | Some t' => Some (DV_Undef t')
      | _ => None
      end
  | EXP_Poison => None
  | OP_IBinop iop t v1 v2 =>
      match (eval_exp s g (Some t) v1, eval_exp s g (Some t) v2) with
      | (Some dv1, Some dv2) => eval_ibinop iop dv1 dv2
      | (_, _) => None
      end
  | OP_ICmp icmp t v1 v2 =>
      match (eval_exp s g (Some t) v1, eval_exp s g (Some t) v2) with
      | (Some dv1, Some dv2) => eval_icmp icmp dv1 dv2
      | (_, _) => None
      end
  | OP_Conversion conv t1 e t2 =>
      match eval_exp s g (Some t1) e with
      | Some dv => convert conv dv t1 t2
      | _ => None
      end
  | OP_Select t1 e1 t2 e2 t3 e3 =>
      match (eval_exp s g (Some t1) e1),
            (eval_exp s g (Some t2) e2),
            (eval_exp s g (Some t3) e3) with
      | Some dv1, Some dv2, Some dv3 =>
          eval_select dv1 dv2 dv3
      | _, _, _ => None
      end
  end
.

Definition eval_constant_exp (t : typ) (e : llvm_exp) : option dynamic_value :=
  eval_exp empty_dv_store empty_dv_store (Some t) e
.

Definition next_inst_counter (ic : inst_counter) (c : llvm_cmd) : inst_counter :=
  mk_inst_counter (ic_fid ic) (ic_bid ic) (get_cmd_id c)
.

Definition next_inst_counter_on_branch (ic : inst_counter) (bid : block_id) (mdl :llvm_module) : option inst_counter :=
  match (find_function mdl (ic_fid ic)) with
  | Some d =>
      match (fetch_block d bid) with
      | Some b =>
          match (get_first_cmd_id b) with
          | Some cid => Some (mk_inst_counter (ic_fid ic) (blk_id b) cid)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end
.

Fixpoint fill_store (ls : dv_store) (gs : dv_store) (l : list (raw_id * function_arg)) : option dv_store :=
  match l with
  | (id, ((t, e), _)) :: tail =>
      match (eval_exp ls gs (Some t) e) with
      | Some dv =>
          match (fill_store ls gs tail) with
          | Some s => Some (id !-> Some dv; s)
          | None => None
          end
      | None => None
      end
  | [] => Some empty_dv_store
  end
.

Definition create_local_store (d : llvm_definition) (ls : dv_store) (gs : dv_store) (args : list function_arg) : option dv_store :=
  match (merge_lists (df_args d) args) with
  | Some l => fill_store ls gs l
  | None => None
  end
.

Fixpoint eval_phi_args ls gs t args pbid : option dynamic_value :=
  match args with
  | (bid, e) :: tail =>
      if raw_id_eqb bid pbid then
        eval_exp ls gs (Some t) e
      else
        eval_phi_args ls gs t tail pbid
  | _ => None
  end
.

Fixpoint get_trailing_cmds_by_cid (l : list llvm_cmd) (cid : cmd_id) : option (list llvm_cmd) :=
  match l with
  | c :: tail =>
      if ((get_cmd_id c) =? cid)%nat then (Some l) else get_trailing_cmds_by_cid tail cid
  | [] => None
  end
.

Definition get_trailing_cmds (d : llvm_definition) (ic : inst_counter) : option (list llvm_cmd) :=
  match (fetch_block d (ic_bid ic)) with
  | Some b => get_trailing_cmds_by_cid (blk_cmds b) (ic_cid ic)
  | _ => None
  end
.

Definition klee_make_symbolic_int32_id := (Name "klee_make_symbolic_int32").
Definition klee_make_symbolic_int32_exp : llvm_exp :=
  EXP_Ident (ID_Global klee_make_symbolic_int32_id).
Definition klee_make_symbolic_int32_type := TYPE_Function (TYPE_I 32) [] false.

Definition klee_assume_id := (Name "klee_assume_bool").
Definition klee_assume_exp : llvm_exp := EXP_Ident (ID_Global klee_assume_id).
Definition klee_assume_type := TYPE_Function TYPE_Void [(TYPE_I 1)] false.

(* TODO: use safe_llvm_expr in other rules *)
Inductive step : state -> state -> Prop :=
  | Step_OP : forall ic cid v e c cs pbid ls stk gs mdl dv,
      (eval_exp ls gs None e) = Some dv ->
      step
        (mk_state
          ic
          (CMD_Inst cid (INSTR_Op v e))
          (c :: cs)
          pbid
          ls
          stk
          gs
          mdl
        )
        (mk_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> Some dv; ls)
          stk
          gs
          mdl
        )
(* TODO: remove
  | Step_UDiv : forall ic cid v exact t e1 e2 c cs pbid ls stk gs mdl di2 dv,
      (eval_exp ls gs (Some t) e2) = Some (DV_Int di2) ->
      (di_is_zero di2) = false ->
      (eval_exp ls gs None (OP_IBinop (UDiv exact) t e1 e2)) = Some dv ->
      step
        (mk_state
          ic
          (CMD_Inst cid (INSTR_Op v (OP_IBinop (UDiv exact) t e1 e2)))
          (c :: cs)
          pbid
          ls
          stk
          gs
          mdl
        )
        (mk_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> Some dv; ls)
          stk
          gs
          mdl
        )
*)
  | Step_Phi : forall ic cid v t args c cs pbid ls stk gs mdl dv,
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
          mdl
        )
        (mk_state
          (next_inst_counter ic c)
          c
          cs
          (Some pbid)
          (v !-> Some dv; ls)
          stk
          gs
          mdl
        )
  | Step_UnconditionalBr : forall ic cid tbid pbid ls stk gs mdl d b c cs,
      (find_function mdl (ic_fid ic)) = Some d ->
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
          mdl
        )
        (mk_state
          (mk_inst_counter (ic_fid ic) tbid (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          mdl
        )
  | Step_Br_True : forall ic cid e bid1 bid2 pbid ls stk gs mdl d b c cs,
      (eval_exp ls gs (Some (TYPE_I 1)) e) = Some dv_true ->
      (find_function mdl (ic_fid ic)) = Some d ->
      (fetch_block d bid1) = Some b ->
      (blk_cmds b) = c :: cs ->
      step
        (mk_state
          ic
          (CMD_Term cid (TERM_Br ((TYPE_I 1), e) bid1 bid2))
          []
          pbid
          ls
          stk
          gs
          mdl
        )
        (mk_state
          (mk_inst_counter (ic_fid ic) bid1 (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          mdl
        )
  | Step_Br_False : forall ic cid e bid1 bid2 pbid ls stk gs mdl d b c cs,
      (eval_exp ls gs (Some (TYPE_I 1)) e) = Some dv_false ->
      (find_function mdl (ic_fid ic)) = Some d ->
      (fetch_block d bid2) = Some b ->
      (blk_cmds b) = c :: cs ->
      step
        (mk_state
          ic
          (CMD_Term cid (TERM_Br ((TYPE_I 1), e) bid1 bid2))
          []
          pbid
          ls
          stk
          gs
          mdl
        )
        (mk_state
          (mk_inst_counter (ic_fid ic) bid2 (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          mdl
        )
  | Step_VoidCall : forall ic cid f args anns c cs pbid ls stk gs mdl d b c' cs' ls',
      (find_function_by_exp mdl f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function TYPE_Void (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (create_local_store d ls gs args) = Some ls' ->
      step
        (mk_state
          ic
          (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, f) args anns))
          (c :: cs)
          pbid
          ls
          stk
          gs
          mdl
        )
        (mk_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          None
          ls'
          ((Frame ls (next_inst_counter ic c) pbid None) :: stk)
          gs
          mdl
        )
  | Step_Call : forall ic cid v t f args anns c cs pbid ls stk gs mdl d b c' cs' ls',
      (find_function_by_exp mdl f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function t (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (create_local_store d ls gs args) = Some ls' ->
      step
        (mk_state
          ic
          (CMD_Inst cid (INSTR_Call v (t, f) args anns))
          (c :: cs)
          pbid
          ls
          stk
          gs
          mdl
        )
        (mk_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          None
          ls'
          ((Frame ls (next_inst_counter ic c) pbid (Some v)) :: stk)
          gs
          mdl
        )
  (* TODO: check the return type of the current function *)
  | Step_RetVoid : forall ic cid pbid ls ls' ic' pbid' stk gs mdl d c' cs',
      (find_function mdl (ic_fid ic')) = Some d ->
      (get_trailing_cmds d ic') = Some (c' :: cs') ->
      step
        (mk_state
          ic
          (CMD_Term cid TERM_RetVoid)
          []
          pbid
          ls
          ((Frame ls' ic' pbid' None) :: stk)
          gs
          mdl
        )
        (mk_state
          ic'
          c'
          cs'
          pbid'
          ls'
          stk
          gs
          mdl
        )
  (* TODO: check the return type of the current function *)
  | Step_Ret : forall ic cid t e pbid ls ls' ic' pbid' v stk gs mdl dv d c' cs',
      (eval_exp ls gs (Some t) e) = Some dv ->
      (find_function mdl (ic_fid ic')) = Some d ->
      (get_trailing_cmds d ic') = Some (c' :: cs') ->
      step
        (mk_state
          ic
          (CMD_Term cid (TERM_Ret (t, e)))
          []
          pbid
          ls
          ((Frame ls' ic' pbid' (Some v)) :: stk)
          gs
          mdl
        )
        (mk_state
          ic'
          c'
          cs'
          pbid'
          (v !-> Some dv; ls')
          stk
          gs
          mdl
        )
  | Step_MakeSymbolicInt32 : forall ic cid v c cs pbid ls stk gs mdl n d,
      (find_function mdl klee_make_symbolic_int32_id) = None ->
      (find_declaration mdl klee_make_symbolic_int32_id) = Some d ->
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
          mdl
        )
        (mk_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> Some (DV_Int (DI_I32 (repr n))); ls)
          stk
          gs
          mdl
        )
  | Step_Assume : forall ic cid e attrs c cs pbid ls stk gs mdl d,
      (find_function mdl klee_assume_id) = None ->
      (find_declaration mdl klee_assume_id) = Some d ->
      (dc_type d) = klee_assume_type ->
      (eval_exp ls gs (Some (TYPE_I 1)) e) = Some dv_true ->
      step
        (mk_state
          ic
          (CMD_Inst cid (INSTR_VoidCall (TYPE_Void, klee_assume_exp) [(((TYPE_I 1), e), attrs)] []))
          (c :: cs)
          pbid
          ls
          stk
          gs
          mdl
        )
        (mk_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          ls
          stk
          gs
          mdl
        )
.

Definition multi_step := multi step.

Definition build_inst_counter (mdl :llvm_module) (d : llvm_definition) : option inst_counter :=
  match (entry_block d) with
  | Some b =>
      match (get_first_cmd_id b) with
      | Some cid => Some (mk_inst_counter (dc_name (df_prototype d)) (blk_id b) cid)
      | _ => None
      end
  | _ => None
  end
.

Definition init_local_store (mdl :llvm_module) (d : llvm_definition) := empty_dv_store.

Definition get_global_initializer (g : llvm_global) : option dynamic_value :=
  match (g_exp g) with
  | Some e => eval_constant_exp (g_typ g) e
  | _ => Some (DV_Undef (g_typ g)) (* TODO: check against the specifiction *)
  end
.

Definition add_global (gs : dv_store) (g : llvm_global) : option dv_store :=
  match (get_global_initializer g) with
  | Some dv => Some ((g_ident g) !-> Some dv; gs)
  | _ => None
  end
.

(* TODO: use later in init_global_store? *)
Fixpoint init_global_store_internal (gs : dv_store) (l : list llvm_global) : option dv_store :=
  match l with
  | g :: tail =>
      match (add_global gs g) with
      | Some gs' => init_global_store_internal gs' tail
      | _ => None
      end
  | [] => Some gs
  end
.

(* TODO: change later? *)
Definition init_global_store (mdl :llvm_module) : dv_store := empty_dv_store.

(* TODO: make sure that there are no parameters *)
Definition init_state (mdl : llvm_module) (fid : function_id) : option state :=
  match (find_function mdl fid) with
  | Some d =>
    match (build_inst_counter mdl d) with
    | Some ic =>
        match (entry_block d) with
        | Some b =>
            match (blk_cmds b) with
            | cmd :: tail =>
                Some (mk_state
                  ic
                  cmd
                  tail
                  None
                  (init_local_store mdl d)
                  []
                  (init_global_store mdl)
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

Inductive is_division : ibinop -> Prop :=
  | Is_Division_UDiv : forall exact, is_division (UDiv exact)
  | Is_Division_SDiv : forall exact, is_division (SDiv exact)
  | Is_Division_URem : is_division URem
  | Is_Division_SRem : is_division SRem
.

Inductive is_shift : ibinop -> Prop :=
  | Is_Shift_Shl : forall nuw nsw, is_shift (Shl nuw nsw)
  | Is_Shift_LShr : forall exact, is_shift (LShr exact)
  | Is_Shift_AShr : forall exact, is_shift (AShr exact)
.

Definition division_error_condition di : bool :=
  di_eq_const di 0
.

Definition division_overflow_error_condition di1 di2 : bool :=
  match di1, di2 with
  | DI_I32 n1, DI_I32 n2 =>
      eq n1 (repr (-2147483648)) && eq n2 (repr (-1))
  | DI_I64 n1, DI_I64 n2 =>
      eq n1 (repr (-9223372036854775808)) && eq n2 (repr (-1))
  | _, _ => false
  end
.

(* TODO: why bitwidth does not work? *)
Definition shift_error_condition di : bool :=
  match di with
  | DI_I1 n => cmpu Cge n (repr 1)
  | DI_I8 n => cmpu Cge n (repr 8)
  | DI_I16 n => cmpu Cge n (repr 16)
  | DI_I24 n => cmpu Cge n (repr 24)
  | DI_I32 n => cmpu Cge n (repr 32)
  | DI_I40 n => cmpu Cge n (repr 40)
  | DI_I48 n => cmpu Cge n (repr 48)
  | DI_I56 n => cmpu Cge n (repr 56)
  | DI_I64 n => cmpu Cge n (repr 64)
  end
.

Inductive error_state : state -> Prop :=
  (* TODO: remove? *)
  | ES_Assert : forall ic cid args anns cs pbid ls stk gs mdl d,
      (find_function mdl assert_id) = None ->
      (find_declaration mdl assert_id) = Some d ->
      (dc_type d) = assert_type ->
      TYPE_Function TYPE_Void (get_arg_types args) false = assert_type ->
      error_state
        (mk_state
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
          mdl
        )
  | ES_Unreachable : forall ic cid cs pbid ls stk gs mdl,
      error_state
        (mk_state
          ic
          (CMD_Term cid TERM_Unreachable)
          cs
          pbid
          ls
          stk
          gs
          mdl
        )
  (* TODO: add assumptions for e1 e2? safe_llvm_expr? *)
  | ES_DivisionByZero : forall ic cid v op t e1 e2 cs pbid ls stk gs mdl di,
      is_division op ->
      (eval_exp ls gs (Some t) e2) = Some (DV_Int di) ->
      division_error_condition di = true ->
      error_state
        (mk_state
          ic
          (CMD_Inst cid (INSTR_Op v (OP_IBinop op t e1 e2)))
          cs
          pbid
          ls
          stk
          gs
          mdl
        )
  | ES_DivisionOverflow : forall ic cid v exact t e1 e2 cs pbid ls stk gs mdl di1 di2,
      (eval_exp ls gs (Some t) e1) = Some (DV_Int di1) ->
      (eval_exp ls gs (Some t) e2) = Some (DV_Int di2) ->
      division_overflow_error_condition di1 di2 = true ->
      error_state
        (mk_state
          ic
          (CMD_Inst cid (INSTR_Op v (OP_IBinop (SDiv exact) t e1 e2)))
          cs
          pbid
          ls
          stk
          gs
          mdl
        )
  (* TODO: add assumptions for e1 e2? safe_llvm_expr? *)
  | ES_OverShift : forall ic cid v op w e1 e2 cs pbid ls stk gs mdl di,
      is_shift op ->
      (eval_exp ls gs (Some (TYPE_I w)) e2) = Some (DV_Int di) ->
      shift_error_condition di = true ->
      error_state
        (mk_state
          ic
          (CMD_Inst cid (INSTR_Op v (OP_IBinop op (TYPE_I w) e1 e2)))
          cs
          pbid
          ls
          stk
          gs
          mdl
        )
.

Definition safe_successors (R : relation state) (s : state) :=
  (forall s', (multi R) s s' -> ~ error_state s').

Definition safe_origin (R : relation state) (s : state) :=
  ~ error_state s /\ safe_successors R s.

Lemma safe_origin_preserved_on_reachability : forall R s s',
  safe_origin R s ->
  (multi R) s s' ->
  safe_origin R s'.
Proof.
  intros R s s' Hsafe Hms.
  unfold safe_origin in *.
  destruct Hsafe as [Hne Hss].
  split.
  {
    unfold safe_successors in Hss.
    apply Hss.
    assumption.
  }
  {
    intros s'' Hms'.
    apply Hss.
    eapply relation_concat.
    { eassumption. }
    { assumption. }
  }
Qed.

Definition is_safe_program (R : relation state) (mdl : llvm_module) (fid : function_id) :=
  exists init_s,
    (init_state mdl fid) = Some init_s /\ (safe_successors R init_s)
.
