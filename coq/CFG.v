(* TODO: rename to LLVMCFG? *)
From Stdlib Require Import Equalities.

From Stdlib Require Import ZArith List String.

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

Section CFG.

  Variable (T:Set).

  Record cfg := mk_cfg {
    init : block_id;
    blks : list (block T);
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

Arguments mk_cfg {_}.
Arguments init {_}.
Arguments blks {_}.
Arguments module {_} _.
Arguments mk_module {_ _}.
Arguments m_name {_ _}.
Arguments m_target {_ _}.
Arguments m_datalayout {_ _}.
Arguments m_type_defs {_ _}.
Arguments m_globals {_ _}.
Arguments m_declarations {_ _}.
Arguments m_definitions {_ _}.

Definition llvm_exp := @exp typ.
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

Definition fetch_block (d : llvm_definition) (bid : block_id) : option llvm_block :=
  find_block (blks (df_body d)) bid
.

Definition entry_block (d : llvm_definition) : option llvm_block :=
  fetch_block d (init (df_body d))
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

Definition find_function_by_exp (m : llvm_module) (e : llvm_exp) : option llvm_definition :=
  match e with
  | EXP_Ident (ID_Global id) => find_function m id
  | _ => None
  end
.

Lemma find_map_match_function_in : forall defs fid d,
  find_map (match_function fid) defs = Some d ->
  In d defs.
Proof.
  intros defs fid d Hfm.
  generalize dependent d; intros d Hfm.
  induction defs as [|d' defs]; simpl in *.
  { discriminate. }
  {
    destruct (match_function fid d') as [d'' | ] eqn:Em.
    {
      left.
      inversion Hfm; subst.
      unfold match_function in Em.
      destruct (dc_name (df_prototype d') =? fid); try discriminate.
      inversion Em; subst.
      reflexivity.
    }
    {
      right.
      apply IHdefs.
      assumption.
    }
  }
Qed.

Lemma find_function_in : forall mdl d fid,
  find_function mdl fid = Some d ->
  In d (m_definitions mdl).
Proof.
  intros mdl d fid Hf.
  unfold find_function in Hf.
  destruct mdl.
  simpl.
  eapply find_map_match_function_in.
  eassumption.
Qed.

Lemma find_block_in : forall bs bid b,
  find_block bs bid = Some b ->
  In b bs.
Proof.
  intros bs bid b Hfb.
  generalize dependent b; intros b Hfb.
  induction bs as [|b' bs]; simpl in *.
  { discriminate. }
  {
    destruct (match_block bid b') eqn:Em.
    {
      left.
      inversion Hfb; subst.
      reflexivity.
    }
    {
      right.
      apply IHbs.
      assumption.
    }
  }
Qed.

Lemma fetch_block_in : forall d bid b,
  fetch_block d bid = Some b ->
  In b (blks (df_body d)).
Proof.
  intros d bid b Hfb.
  unfold fetch_block in Hfb.
  destruct d.
  simpl in *.
  destruct df_body.
  simpl in *.
  eapply find_block_in.
  eassumption.
Qed.
