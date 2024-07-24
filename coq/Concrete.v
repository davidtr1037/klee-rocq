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
From SE.Utils Require Import ListUtil.

Record inst_counter := mk_inst_counter {
  fid : function_id;
  bid : block_id;
  cid : cmd_id;
}.

Definition dv_store := total_map dynamic_value.

Definition empty_dv_store := empty_map DV_Undef.

Definition global_store := dv_store.

(*
Record frame := mk_frame {
  local_store : store;
  return_ic : inst_counter;
  return_var : raw_id;
}.
*)

Inductive frame : Type :=
  | Frame (s : dv_store) (ic : inst_counter) (v : raw_id)
  | Frame_NoReturn (s : dv_store) (ic : inst_counter)
.

(* TODO: define as an inductive type? *)
Record state : Type := mk_state {
  ic : inst_counter;
  cmd : llvm_cmd;
  block : list llvm_cmd;
  store : dv_store; (* TODO: rename *)
  stack : list frame;
  globals : global_store;
  module : llvm_module;
}.

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

Definition build_local_store (m : llvm_module) (d : llvm_definition) := empty_dv_store.

Definition get_global_initializer (g : llvm_global) : option dynamic_value :=
  match (g_exp g) with
  | Some e =>
      match (eval_constant_exp (g_typ g) e) with
      | Some dv => Some dv
      | _ => None
      end
  | _ => Some DV_Undef (* TODO: check against the specifiction *)
  end
.

Definition add_global (gs : global_store) (g : llvm_global) : option global_store :=
  match (get_global_initializer g) with
  | Some dv => Some ((g_ident g) !-> dv; gs)
  | _ => None
  end
.

Fixpoint build_global_store_internal (gs : global_store) (l : list llvm_global) : option global_store :=
  match l with
  | g :: tail =>
      match (add_global gs g) with
      | Some gs' => build_global_store_internal gs' tail
      | _ => None
      end
  | [] => Some gs
  end
.

Definition build_global_store (m : llvm_module) : option global_store :=
  build_global_store_internal empty_dv_store (m_globals m)
.

(* TODO: assumes that there are no parameters *)
Definition init_state (m : llvm_module) (d : llvm_definition) : option state :=
  match (build_global_store m) with
  | Some gs =>
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
                  (build_local_store m d)
                  []
                  gs
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

Definition lookup_ident (s : dv_store) (g : global_store) (id : ident) : dynamic_value :=
  match id with
  | ID_Local x => s x
  | ID_Global x => g x
  end
.

(* TODO: why vellvm passes dtyp? *)
Fixpoint eval_exp (s : dv_store) (g : global_store) (t : option typ) (e : exp typ) : option dynamic_value :=
  match e with
  | EXP_Ident id => Some (lookup_ident s g id)
  | EXP_Integer n =>
      match t with
      | Some (TYPE_I bits) => make_dv bits n
      | _ => None
      end
  | EXP_Float f => None
  | EXP_Double f => None
  | EXP_Hex f => None
  | EXP_Bool b => Some (make_bool b)
  | EXP_Null => None
  | EXP_Zero_initializer => None
  | EXP_Cstring elts => None
  | EXP_Undef => Some DV_Undef
  | EXP_Poison => None
  | EXP_Struct fields => None
  | EXP_Packed_struct fields => None
  | EXP_Array elts => None
  | EXP_Vector elts => None
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
  | OP_FBinop fop _ _ _ _ => None
  | OP_FCmp _ _ _ _ => None
  | OP_Conversion conv t1 e t2 =>
      match eval_exp s g (Some t1) e with
      | Some dv => convert conv dv t1 t2
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

Definition next_inst_counter (pc : inst_counter) (c : llvm_cmd) : inst_counter :=
  mk_inst_counter (fid pc) (bid pc) (get_cmd_id c)
.

Definition next_inst_counter_on_branch (pc : inst_counter) (bid : block_id) (m : llvm_module) : option inst_counter :=
  match (find_function m (fid pc)) with
  | Some d =>
      match (fetch_block d bid) with
      | Some b =>
          match (get_first_cmd_id b) with
          | Some cid => Some (mk_inst_counter (fid pc) (blk_id b) cid)
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

Fixpoint get_arg_types (args : list (function_arg)) : list typ :=
  match args with
  | ((t, e), _) :: tail => t :: get_arg_types tail
  | [] => []
  end
.

Fixpoint eval_args (s : dv_store) (g : global_store) (args : list function_arg) : option (list dynamic_value) :=
  match args with
  | ((t, e), _) :: tail =>
      match (eval_exp s g (Some t) e) with
      | Some dv =>
          match (eval_args s g tail) with
          | Some dvs => Some (dv :: dvs)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end
.

Fixpoint fill_store (l : list (raw_id * dynamic_value)) : dv_store :=
  match l with
  | (id, dv) :: tail => (id !-> dv; (fill_store tail))
  | [] => empty_dv_store
  end
.

Definition init_local_store (d : llvm_definition) (dvs : list dynamic_value) : option dv_store :=
  match (merge_lists (df_args d) dvs) with
  | Some l => Some (fill_store l)
  | None => None
  end
.

Inductive step : state -> state -> Prop :=
  | Step_OP : forall pc cid v e c b ls stk gs m dv,
      (eval_exp ls gs None e) = Some dv ->
      step
        (mk_state
          pc
          (CMD_Inst cid (INSTR_Op v e))
          (c :: b)
          ls
          stk
          gs
          m
        )
        (mk_state
          (next_inst_counter pc c)
          c
          b
          (v !-> dv; ls)
          stk
          gs
          m
        )
  | Step_UnconditionalBr : forall pc cid bid ls stk gs m d b c cs,
      (find_function m (fid pc)) = Some d ->
      (fetch_block d bid) = Some b ->
      (blk_cmds b) = c :: cs ->
      step
        (mk_state pc
          (CMD_Term cid (TERM_UnconditionalBr bid))
          []
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (fid pc) bid (get_cmd_id c))
          c
          cs
          ls
          stk
          gs
          m
        )
  | Step_Br_True : forall pc cid t e bid1 bid2 ls stk gs m d b c cs,
      (eval_exp ls gs (Some t) e) = Some (DV_I1 one) ->
      (find_function m (fid pc)) = Some d ->
      (fetch_block d bid1) = Some b ->
      (blk_cmds b) = c :: cs ->
      step
        (mk_state
          pc
          (CMD_Term cid (TERM_Br (t, e) bid1 bid2))
          []
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (fid pc) bid1 (get_cmd_id c))
          c
          cs
          ls
          stk
          gs
          m
        )
  | Step_Br_False : forall pc cid t e bid1 bid2 ls stk gs m d b c cs,
      (eval_exp ls gs (Some t) e) = Some (DV_I1 zero) ->
      (find_function m (fid pc)) = Some d ->
      (fetch_block d bid2) = Some b ->
      (blk_cmds b) = c :: cs ->
      step
        (mk_state
          pc
          (CMD_Term cid (TERM_Br (t, e) bid1 bid2))
          []
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (fid pc) bid2 (get_cmd_id c))
          c
          cs
          ls
          stk
          gs
          m
        )
  (* TODO: t must be TYPE_Void here? *)
  | Step_VoidCall : forall pc cid t f args anns c cs ls stk gs m d b c' cs' dvs s',
      (find_function_by_exp m f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function t (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (eval_args ls gs args) = Some dvs ->
      (init_local_store d  dvs) = Some s' ->
      step
        (mk_state
          pc
          (CMD_Inst cid (INSTR_VoidCall (t, f) args anns))
          (c :: cs)
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          s'
          ((Frame_NoReturn ls (next_inst_counter pc c)) :: stk)
          gs
          m
        )
  | Step_Call : forall pc cid v t f args anns c cs ls stk gs m d b c' cs' dvs s',
      (find_function_by_exp m f) = Some d ->
      (dc_type (df_prototype d)) = TYPE_Function t (get_arg_types args) false ->
      (entry_block d) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      (eval_args ls gs args) = Some dvs ->
      (init_local_store d dvs) = Some s' ->
      step
        (mk_state
          pc
          (CMD_Inst cid (INSTR_Call v (t, f) args anns))
          (c :: cs)
          ls
          stk
          gs
          m
        )
        (mk_state
          (mk_inst_counter (get_fid d) (blk_id b) (get_cmd_id c'))
          c'
          cs'
          s'
          ((Frame ls (next_inst_counter pc c) v) :: stk)
          gs
          m
        )
  (* TODO: check the return type of the current function *)
  | Step_RetVoid : forall pc cid ls ls' pc' stk gs m d b c' cs',
      (find_function m (fid pc)) = Some d ->
      (fetch_block d (bid pc)) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      step
        (mk_state
          pc
          (CMD_Term cid TERM_RetVoid)
          []
          ls
          ((Frame_NoReturn ls' pc') :: stk)
          gs
          m
        )
        (mk_state
          pc'
          c'
          cs'
          ls'
          stk
          gs
          m
        )
  (* TODO: check the return type of the current function *)
  | Step_Ret : forall pc cid t e ls ls' pc' v stk gs m dv d b c' cs',
      (eval_exp ls gs (Some t) e) = Some dv ->
      (find_function m (fid pc)) = Some d ->
      (fetch_block d (bid pc)) = Some b ->
      (blk_cmds b) = c' :: cs' ->
      step
        (mk_state
          pc
          (CMD_Term cid (TERM_Ret (t, e)))
          []
          ls
          ((Frame ls' pc' v) :: stk)
          gs
          m
        )
        (mk_state
          pc'
          c'
          cs'
          (v !-> dv; ls')
          stk
          gs
          m
        )
.
