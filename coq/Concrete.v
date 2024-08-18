(* TODO: do something with exp typ *)
From Coq Require Import List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import CFG.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.
From SE Require Import Relation.

From SE.Utils Require Import ListUtil.

Record inst_counter := mk_inst_counter {
  ic_fid : function_id;
  ic_bid : block_id;
  ic_cid : cmd_id;
}.

Definition dv_store := total_map (option dynamic_value).

Definition empty_dv_store : dv_store := empty_map None.

Inductive frame : Type :=
  | Frame (s : dv_store) (ic : inst_counter) (pbid : option block_id) (v : raw_id)
  | Frame_NoReturn (s : dv_store) (ic : inst_counter) (pbid : option block_id)
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
Definition assert_exp : exp typ := (EXP_Ident (ID_Global assert_id)).
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

(* TODO: handle TERM_Unreachable? *)
Inductive error_state : state -> Prop :=
  | ES_Assert : forall ic cid args anns cs pbid ls stk gs m d,
      (find_function m assert_id) = None ->
      (find_declaration m assert_id) = Some d ->
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
          m
       )
.

Definition lookup_ident (s : dv_store) (g : dv_store) (id : ident) : option dynamic_value :=
  match id with
  | ID_Local x => s x
  | ID_Global x => g x
  end
.

(* TODO: why vellvm passes dtyp? *)
Fixpoint eval_exp (s : dv_store) (g : dv_store) (t : option typ) (e : exp typ) : option dynamic_value :=
  match e with
  | EXP_Ident id => lookup_ident s g id
  | EXP_Integer n =>
      match t with
      | Some (TYPE_I bits) => make_dv bits n
      | _ => None
      end
  | EXP_Bool b => Some (make_bool b)
  | EXP_Null => None
  | EXP_Zero_initializer => None
  | EXP_Undef => Some DV_Undef
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
  | OP_Select _ _ _ => None
  end
.

Definition eval_constant_exp (t : typ) (e : exp typ) : option dynamic_value :=
  eval_exp empty_dv_store empty_dv_store (Some t) e
.

Definition next_inst_counter (ic : inst_counter) (c : llvm_cmd) : inst_counter :=
  mk_inst_counter (ic_fid ic) (ic_bid ic) (get_cmd_id c)
.

Definition next_inst_counter_on_branch (ic : inst_counter) (bid : block_id) (m : llvm_module) : option inst_counter :=
  match (find_function m (ic_fid ic)) with
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

Definition find_function_by_exp (m : llvm_module) (e : exp typ) : option llvm_definition :=
  match e with
  | EXP_Ident (ID_Global id) => find_function m id
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

Fixpoint get_trailing_cmds_by_cid (l : list llvm_cmd) (cid : cmd_id) :=
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
Definition klee_make_symbolic_int32_exp : exp typ :=
  EXP_Ident (ID_Global klee_make_symbolic_int32_id).
Definition klee_make_symbolic_int32_type := TYPE_Function (TYPE_I 32) [] false.

Definition klee_assume_id := (Name "klee_assume").
Definition klee_assume_exp : exp typ := EXP_Ident (ID_Global klee_assume_id).
Definition klee_assume_type := TYPE_Function TYPE_Void [(TYPE_I 64)] false.

Inductive step : state -> state -> Prop :=
  | Step_OP : forall ic cid v e c cs pbid ls stk gs m dv,
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
          m
        )
        (mk_state
          (next_inst_counter ic c)
          c
          cs
          pbid
          (v !-> Some dv; ls)
          stk
          gs
          m
        )
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
          (v !-> Some dv; ls)
          stk
          gs
          m
        )
  | Step_UnconditionalBr : forall ic cid tbid pbid ls stk gs m d b c cs,
      (find_function m (ic_fid ic)) = Some d ->
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
          (mk_inst_counter (ic_fid ic) tbid (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          m
        )
  | Step_Br_True : forall ic cid e bid1 bid2 pbid ls stk gs m d b c cs,
      (eval_exp ls gs (Some (TYPE_I 1)) e) = Some dv_true ->
      (find_function m (ic_fid ic)) = Some d ->
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
          m
        )
        (mk_state
          (mk_inst_counter (ic_fid ic) bid1 (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          m
        )
  | Step_Br_False : forall ic cid e bid1 bid2 pbid ls stk gs m d b c cs,
      (eval_exp ls gs (Some (TYPE_I 1)) e) = Some dv_false ->
      (find_function m (ic_fid ic)) = Some d ->
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
          m
        )
        (mk_state
          (mk_inst_counter (ic_fid ic) bid2 (get_cmd_id c))
          c
          cs
          (Some (ic_bid ic))
          ls
          stk
          gs
          m
        )
  | Step_VoidCall : forall ic cid f args anns c cs pbid ls stk gs m d b c' cs' ls',
      (find_function_by_exp m f) = Some d ->
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
  | Step_Call : forall ic cid v t f args anns c cs pbid ls stk gs m d b c' cs' ls',
      (find_function_by_exp m f) = Some d ->
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
          m
        )
        (mk_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          None
          ls'
          ((Frame ls (next_inst_counter ic c) pbid v) :: stk)
          gs
          m
        )
  (* TODO: check the return type of the current function *)
  | Step_RetVoid : forall ic cid pbid ls ls' ic' pbid' stk gs m d c' cs',
      (find_function m (ic_fid ic')) = Some d ->
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
      (find_function m (ic_fid ic')) = Some d ->
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
          (v !-> Some dv; ls')
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
          (v !-> Some (DV_Int (DI_I32 (repr n))); ls)
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

Definition multi_step := multi step.

Definition build_inst_counter (m : llvm_module) (d : llvm_definition) : option inst_counter :=
  match (entry_block d) with
  | Some b =>
      match (get_first_cmd_id b) with
      | Some cid => Some (mk_inst_counter (dc_name (df_prototype d)) (blk_id b) cid)
      | _ => None
      end
  | _ => None
  end
.

Definition init_local_store (m : llvm_module) (d : llvm_definition) := empty_dv_store.

Definition get_global_initializer (g : llvm_global) : option dynamic_value :=
  match (g_exp g) with
  | Some e => eval_constant_exp (g_typ g) e
  | _ => Some DV_Undef (* TODO: check against the specifiction *)
  end
.

Definition add_global (gs : dv_store) (g : llvm_global) : option dv_store :=
  match (get_global_initializer g) with
  | Some dv => Some ((g_ident g) !-> Some dv; gs)
  | _ => None
  end
.

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
Definition init_global_store (m : llvm_module) : dv_store := empty_dv_store.

(* TODO: assumes that there are no parameters *)
Definition init_state (m : llvm_module) (d : llvm_definition) : option state :=
  match (build_inst_counter m d) with
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
                (init_local_store m d)
                []
                (init_global_store m)
                m
              )
          | _ => None
          end
      | None => None
      end
  | None => None
  end
.

Lemma init_state_preserves_module : forall mdl d s,
  init_state mdl d = Some s -> module s = mdl.
Proof.
  intros mdl d s H.
  unfold init_state in H.
  destruct (build_inst_counter mdl d) as [c_ic | ] eqn:Ec_ic; try discriminate H.
  destruct (entry_block d) as [c_b | ] eqn:Ec_b; try discriminate H.
  destruct (blk_cmds c_b) as [ | c_cmd c_cmds ] eqn:Ec_cs; try discriminate H.
  inversion H; subst.
  reflexivity.
Qed.

Definition is_safe_program (mdl : llvm_module) (d : llvm_definition) :=
  exists init_s,
    (init_state mdl d) = Some init_s /\ (forall s, multi_step init_s s -> ~ error_state s)
.
