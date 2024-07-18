From SE Require Import BitVectors.
From SE Require Import DynamicValue.
From SE Require Import IDMap.
From SE Require Import LLVMAst.

(* TODO: rename? *)
Definition env := total_map (option dynamic_value).

Definition global_env := env.

Definition frame := env.

Definition stack := list frame.

Record state : Type := mkState {
  globals : global_env;
  current_frame : frame;
  call_stack : stack
}.

(* Definition init_state ... *)

Definition lookup_ident (s : state) (id : ident) : option dynamic_value :=
  match id with
  | ID_Local x => (current_frame s) x
  | ID_Global x => (globals s) x
  end
.

(* TODO: why vellvm passes dtyp? *)
Fixpoint eval_exp (s : state) (t : typ) (e : exp typ) : option dynamic_value :=
  match e with
  | EXP_Ident id => lookup_ident s id
  | EXP_Integer n =>
      match t with
      | TYPE_I bits => make_dv bits n
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
      match (eval_exp s t v1, eval_exp s t v2) with
      | (Some dv1, Some dv2) => eval_ibinop iop dv1 dv2
      | (_, _) => None
      end
  | OP_ICmp icmp t v1 v2 =>
      match (eval_exp s t v1, eval_exp s t v2) with
      | (Some dv1, Some dv2) => eval_icmp icmp dv1 dv2
      | (_, _) => None
      end
  | OP_FBinop fop _ _ _ _ => None
  | OP_FCmp _ _ _ _ => None
  | OP_Conversion conv t1 e t2 =>
      match eval_exp s t1 e with
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

Inductive step : state -> state -> Prop :=
.
