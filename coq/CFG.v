(* begin hide *)
Require Import Equalities.

From Coq Require Import ZArith List String.

From SE Require Import
     Utilities
     LLVMAst.

From ExtLib Require Import
     Programming.Eqv
     Structures.Monads.

Import ListNotations.
Import EqvNotation.
Import MonadNotation.
Open Scope list.
Open Scope monad_scope.
(* end hide *)

Section CFG.

  Variable (T:Set).

  (* TODO: rename to mk_cfg *)
  Record cfg := mkCFG {
    init : block_id;
    blks : list (block T);
    args : list raw_id;
  }.

  Record module {Body : Set} : Set := mk_module {
    m_name : option string;
    m_target : option string;
    m_datalayout : option string;
    m_type_defs : list (ident * T);
    m_globals : list (global T);
    m_declarations : list (declaration T);
    m_definitions : list (@definition T Body);
  }.

End CFG.

Arguments mkCFG {_}.
Arguments init {_}.
Arguments blks {_}.
Arguments args {_}.
Arguments module {_} _.
Arguments mk_module {_ _}.
Arguments m_name {_ _}.
Arguments m_target {_ _}.
Arguments m_datalayout {_ _}.
Arguments m_type_defs {_ _}.
Arguments m_globals {_ _}.
Arguments m_declarations {_ _}.
Arguments m_definitions {_ _}.

Definition llvm_global := @global typ.
Definition llvm_cmd := @cmd typ.
Definition llvm_block := @block typ.
Definition llvm_cfg := @cfg typ.
Definition llvm_declaration := @declaration typ.
Definition llvm_definition := @definition typ llvm_cfg.
Definition llvm_module : Set := @module typ llvm_cfg.

Definition get_cmd_id (c : llvm_cmd) : cmd_id :=
  match c with
  | CMD_Phi n _ => n
  | CMD_Inst n _ => n
  | CMD_Term n _ => n
  end
.

Definition get_first_cmd (b : llvm_block) : option cmd :=
  match (blk_cmds b) with
  | c :: _ => Some c
  | _ => None
  end
.

Definition get_first_cmd_id (b : llvm_block) : option cmd_id :=
  match (get_first_cmd b) with
  | Some c => Some (get_cmd_id c)
  | _ => None
  end
.

Definition match_block (bid : block_id) (b : llvm_block) : bool :=
  if (blk_id b) =? bid then true else false
.

Definition find_block (bs: list (llvm_block)) (bid : block_id) : option (llvm_block) :=
  find (fun b => match_block bid b) bs
.

(* TODO: rename *)
Definition get_fid(d : llvm_definition) : function_id :=
  (dc_name (df_prototype d))
.

Definition entry_block (d : llvm_definition) : option llvm_block :=
  find_block (blks (df_body d)) (init (df_body d))
.

Definition fetch_block (d : llvm_definition) (bid : block_id) : option llvm_block :=
  find_block (blks (df_body d)) bid
.

Definition match_declaration (fid : function_id) (d : llvm_declaration) : option (llvm_declaration) :=
  if (dc_name d) =? fid then Some d else None
.

Definition find_declaration (m : llvm_module) (fid : function_id) : option (llvm_declaration) :=
  find_map (match_declaration fid) (m_declarations m)
.

Definition match_function (fid : function_id) (d : llvm_definition) : option (llvm_definition) :=
  if (dc_name (df_prototype d)) =? fid then Some d else None
.

Definition find_function (m : llvm_module) (fid : function_id) : option (llvm_definition) :=
  find_map (match_function fid) (m_definitions m)
.
