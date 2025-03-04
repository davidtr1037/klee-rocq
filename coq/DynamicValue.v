(* TODO: rename module/type? *)
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE.Numeric Require Import Integers.
From SE Require Import LLVMAst.

(* this type represents an LLVM value *)
Inductive dynamic_value : Type :=
  | DV_Int (di : dynamic_int)
  | DV_Undef (t : typ)
  | DV_Poison (t : typ)
.

Inductive is_undef : dynamic_value -> Prop :=
  Is_Undef : forall t, is_undef (DV_Undef t)
.

Inductive is_poison : dynamic_value -> Prop :=
  Is_Poison : forall t, is_poison (DV_Poison t)
.

Class ConvertToDV I : Type := {
  to_dvalue : I -> dynamic_value;
}.

Global Instance ConvertToDVInt1 : ConvertToDV Int1.int := {
  to_dvalue := fun x => DV_Int (DI_I1 x);
}.

Global Instance ConvertToDVInt8 : ConvertToDV Int8.int := {
  to_dvalue := fun x => DV_Int (DI_I8 x);
}.

Global Instance ConvertToDVInt16 : ConvertToDV Int16.int := {
  to_dvalue := fun x => DV_Int (DI_I16 x);
}.

Global Instance ConvertToDVInt32 : ConvertToDV Int32.int := {
  to_dvalue := fun x => DV_Int (DI_I32 x);
}.

Global Instance ConvertToDVInt64 : ConvertToDV Int64.int := {
  to_dvalue := fun x => DV_Int (DI_I64 x);
}.

Definition dv_true := DV_Int di_true.
Definition dv_false := DV_Int di_false.

Definition type_of_int {Int} `{VInt Int} :=
  TYPE_I (Pos.of_nat bitwidth)
.

(* TODO: compare with the latest version *)
Definition eval_ibinop_generic {Int} `{VInt Int} `{ConvertToDV Int} (op : ibinop) (x y : Int) : option dynamic_value :=
  match op with
  | Add nuw nsw =>
    if orb (andb nuw (eq (add_carry x y zero) one))
           (andb nsw (eq (add_overflow x y zero) one)) then
      Some (DV_Poison type_of_int)
    else
      Some (to_dvalue (add x y))
  | Sub nuw nsw =>
    if orb (andb nuw (eq (sub_borrow x y zero) one))
           (andb nsw (eq (sub_overflow x y zero) one)) then
      Some (DV_Poison type_of_int)
    else
      Some (to_dvalue (sub x y))
  | Mul nuw nsw =>
    if (bitwidth =? 1)%nat then
      Some (to_dvalue (mul x y))
    else
      let res := mul x y in
      let res_s' := ((signed x) * (signed y))%Z in
      if orb (andb nuw ((unsigned x) * (unsigned y) >? unsigned res)%Z)
             (andb nsw (orb (min_signed >? res_s')%Z (res_s' >? max_signed)%Z)) then
        Some (DV_Poison type_of_int)
      else
        Some (to_dvalue res)
  | Shl nuw nsw =>
    if (bitwidth =? 1)%nat then
      if ((unsigned y) >=? 1)%Z then
        Some (DV_Poison type_of_int)
      else
        Some (to_dvalue x)
    else
      let bz := Z.of_nat bitwidth in
      let res := shl x y in
      let res_u := unsigned res in
      let res_u' := Z.shiftl (unsigned x) (unsigned y) in
      if ((unsigned y) >=? bz)%Z then
        Some (DV_Poison type_of_int)
      else if orb (andb nuw (res_u' >? res_u)%Z)
                  (andb nsw (negb (Z.shiftr (unsigned x) (bz - unsigned y) =? ((unsigned (negative res)) * (Z.pow 2 (unsigned y) - 1)))%Z)) then
        Some (DV_Poison type_of_int)
      else
        Some (to_dvalue res)
  | UDiv ex =>
    (* TODO: should be undefined behavior *)
    if (unsigned y =? 0)%Z then None
    else
      if andb ex (negb ((unsigned x) mod (unsigned y) =? 0)%Z) then
        Some (DV_Poison type_of_int)
      else
        Some (to_dvalue (divu x y))
  | SDiv ex =>
    (* TODO: should be undefined behavior *)
    if (signed y =? 0)%Z then None
    else
      if andb ex (negb (((signed x) mod (signed y)) =? 0)%Z) then
        Some (DV_Poison type_of_int)
      else
        Some (to_dvalue (divs x y))
  | LShr ex =>
    if (bitwidth =? 1)%nat then
      if ((unsigned y) >=? 1)%Z then
        Some (DV_Poison type_of_int)
      else
        Some (to_dvalue x)
    else
      let bz := Z.of_nat bitwidth in
      if ((unsigned y) >=? bz)%Z then
        Some (DV_Poison type_of_int)
      else if andb ex (negb ((unsigned x) mod (Z.pow 2 (unsigned y)) =? 0)%Z) then
        Some (DV_Poison type_of_int)
      else
        Some (to_dvalue (shru x y))
  | AShr ex =>
    if (bitwidth =? 1)%nat then
      if ((unsigned y) >=? 1)%Z then
        Some (DV_Poison type_of_int)
      else
        Some (to_dvalue x)
    else
      let bz := Z.of_nat bitwidth in
      if ((unsigned y) >=? bz)%Z then
        Some (DV_Poison type_of_int)
      else if andb ex (negb ((unsigned x) mod (Z.pow 2 (unsigned y)) =? 0)%Z) then
        Some (DV_Poison type_of_int)
     else
       Some (to_dvalue (shr x y))
  | URem =>
      if (unsigned y =? 0)%Z then None else Some (to_dvalue (modu x y))
  | SRem =>
      if (signed y =? 0)%Z then None else Some (to_dvalue (mods x y))
  | And => Some (to_dvalue (and x y))
  | Or => Some (to_dvalue (or x y))
  | Xor => Some (to_dvalue (xor x y))
  end
.

Definition make_bool (b : bool) : dynamic_value :=
  match b with
  | true => dv_true
  | false => dv_false
  end
.

Definition make_dv (bits : positive) (n : Z) : option dynamic_value :=
  match bits with
  | 1%positive => Some (DV_Int (DI_I1 (Int1.repr n)))
  | 8%positive => Some (DV_Int (DI_I8 (Int8.repr n)))
  | 16%positive => Some (DV_Int (DI_I16 (Int16.repr n)))
  | 24%positive => Some (DV_Int (DI_I24 (Int24.repr n)))
  | 32%positive => Some (DV_Int (DI_I32 (Int32.repr n)))
  | 48%positive => Some (DV_Int (DI_I48 (Int48.repr n)))
  | 56%positive => Some (DV_Int (DI_I56 (Int56.repr n)))
  | 64%positive => Some (DV_Int (DI_I64 (Int64.repr n)))
  | _ => None
  end
.

Definition eval_ibinop (op : ibinop) (dv1 dv2 : dynamic_value) : option dynamic_value :=
  match (dv1, dv2) with
  | (DV_Int (DI_I1 n1),  DV_Int (DI_I1 n2))
  | (DV_Int (DI_I8 n1),  DV_Int (DI_I8 n2))
  | (DV_Int (DI_I16 n1), DV_Int (DI_I16 n2))
  | (DV_Int (DI_I32 n1), DV_Int (DI_I32 n2))
  | (DV_Int (DI_I64 n1), DV_Int (DI_I64 n2)) => eval_ibinop_generic op n1 n2
  | (DV_Poison t, _) => Some (DV_Poison t)
  | (_, DV_Poison t) =>
      (* division by poison is undefined behavior *)
      match op with
      | UDiv _ => None
      | SDiv _ => None
      | URem => None
      | SRem => None
      | _ => Some (DV_Poison t)
      end
  | _ => None
  end
.

Definition icmp_to_comparison (op : icmp) : comparison :=
  match op with
  | Eq => Ceq
  | Ne => Cne
  | Ugt => Cgt
  | Uge => Cge
  | Ult => Clt
  | Ule => Cle
  | Sgt => Cgt
  | Sge => Cge
  | Slt => Clt
  | Sle => Cle
  end
.

Definition eval_cmp_result {Int} `{VInt Int} (op : icmp) (x y : Int) : bool :=
  match op with
  | Ugt
  | Uge
  | Ult
  | Ule =>
    cmpu (icmp_to_comparison op) x y
  |_ =>
    cmp (icmp_to_comparison op) x y
  end
.

(* TODO: compare with the latest version *)
Definition eval_icmp_generic {Int} `{VInt Int} (op : icmp) (x y : Int) : dynamic_value :=
  DV_Int (if (eval_cmp_result op x y) then di_true else di_false)
.

Definition eval_icmp (op : icmp) (v1 v2 : dynamic_value) : option dynamic_value :=
  match (v1, v2) with
  | (DV_Int (DI_I1 n1),  DV_Int (DI_I1 n2))
  | (DV_Int (DI_I8 n1),  DV_Int (DI_I8 n2))
  | (DV_Int (DI_I16 n1), DV_Int (DI_I16 n2))
  | (DV_Int (DI_I32 n1), DV_Int (DI_I32 n2))
  | (DV_Int (DI_I64 n1), DV_Int (DI_I64 n2)) => Some (eval_icmp_generic op n1 n2)
  | (DV_Poison t, _) => Some (DV_Poison (TYPE_I 1))
  | (_, DV_Poison t) => Some (DV_Poison (TYPE_I 1))
  | _ => None
  end
.

(* TODO: compare with the latest version *)
Definition convert conv x t1 t2 : option dynamic_value :=
  match conv with
  | Zext =>
      match t1, x, t2 with
      (* i8 *)
      | TYPE_I 1, DV_Int (DI_I1 i1), TYPE_I 8 =>
          Some (DV_Int (DI_I8 (repr (unsigned i1))))
      (* i16 *)
      | TYPE_I 1, DV_Int (DI_I1 i1), TYPE_I 16 =>
          Some (DV_Int (DI_I16 (repr (unsigned i1))))
      | TYPE_I 8, DV_Int (DI_I8 i1), TYPE_I 16 =>
          Some (DV_Int (DI_I16 (repr (unsigned i1))))
      (* i32 *)
      | TYPE_I 1, DV_Int (DI_I1 i1), TYPE_I 32 =>
          Some (DV_Int (DI_I32 (repr (unsigned i1))))
      | TYPE_I 8, DV_Int (DI_I8 i1), TYPE_I 32 =>
          Some (DV_Int (DI_I32 (repr (unsigned i1))))
      | TYPE_I 16, DV_Int (DI_I16 i1), TYPE_I 32 =>
          Some (DV_Int (DI_I32 (repr (unsigned i1))))
      (* i64 *)
      | TYPE_I 1, DV_Int (DI_I1 i1), TYPE_I 64 =>
          Some (DV_Int (DI_I64 (repr (unsigned i1))))
      | TYPE_I 8, DV_Int (DI_I8 i1), TYPE_I 64 =>
          Some (DV_Int (DI_I64 (repr (unsigned i1))))
      | TYPE_I 16, DV_Int (DI_I16 i1), TYPE_I 64 =>
          Some (DV_Int (DI_I64 (repr (unsigned i1))))
      | TYPE_I 32, DV_Int (DI_I32 i1), TYPE_I 64 =>
          Some (DV_Int (DI_I64 (repr (unsigned i1))))
      | _, DV_Poison _, t => Some (DV_Poison t)
      | _, _, _ => None
      end
  | Sext =>
      match t1, x, t2 with
      (* i8 *)
      | TYPE_I 1, DV_Int (DI_I1 i1), TYPE_I 8 =>
          Some (DV_Int (DI_I8 (repr (signed i1))))
      (* i16 *)
      | TYPE_I 1, DV_Int (DI_I1 i1), TYPE_I 16 =>
          Some (DV_Int (DI_I16 (repr (signed i1))))
      | TYPE_I 8, DV_Int (DI_I8 i1), TYPE_I 16 =>
          Some (DV_Int (DI_I16 (repr (signed i1))))
      (* i32 *)
      | TYPE_I 1, DV_Int (DI_I1 i1), TYPE_I 32 =>
          Some (DV_Int (DI_I32 (repr (signed i1))))
      | TYPE_I 8, DV_Int (DI_I8 i1), TYPE_I 32 =>
          Some (DV_Int (DI_I32 (repr (signed i1))))
      | TYPE_I 16, DV_Int (DI_I16 i1), TYPE_I 32 =>
          Some (DV_Int (DI_I32 (repr (signed i1))))
      (* i64 *)
      | TYPE_I 1, DV_Int (DI_I1 i1), TYPE_I 64 =>
          Some (DV_Int (DI_I64 (repr (signed i1))))
      | TYPE_I 8, DV_Int (DI_I8 i1), TYPE_I 64 =>
          Some (DV_Int (DI_I64 (repr (signed i1))))
      | TYPE_I 16, DV_Int (DI_I16 i1), TYPE_I 64 =>
          Some (DV_Int (DI_I64 (repr (signed i1))))
      | TYPE_I 32, DV_Int (DI_I32 i1), TYPE_I 64 =>
          Some (DV_Int (DI_I64 (repr (signed i1))))
      | _, DV_Poison _, t => Some (DV_Poison t)
      | _, _, _ => None
      end
  | Trunc =>
      match t1, x, t2 with
      (* i1 *)
      | TYPE_I 8, DV_Int (DI_I8 i1), TYPE_I 1 =>
          Some (DV_Int (DI_I1 (repr (unsigned i1))))
      | TYPE_I 16, DV_Int (DI_I16 i1), TYPE_I 1 =>
          Some (DV_Int (DI_I1 (repr (unsigned i1))))
      | TYPE_I 32, DV_Int (DI_I32 i1), TYPE_I 1 =>
          Some (DV_Int (DI_I1 (repr (unsigned i1))))
      | TYPE_I 64, DV_Int (DI_I64 i1), TYPE_I 1 =>
          Some (DV_Int (DI_I1 (repr (unsigned i1))))
      (* i8 *)
      | TYPE_I 16, DV_Int (DI_I16 i1), TYPE_I 8 =>
          Some (DV_Int (DI_I8 (repr (unsigned i1))))
      | TYPE_I 32, DV_Int (DI_I32 i1), TYPE_I 8 =>
          Some (DV_Int (DI_I8 (repr (unsigned i1))))
      | TYPE_I 64, DV_Int (DI_I64 i1), TYPE_I 8 =>
          Some (DV_Int (DI_I8 (repr (unsigned i1))))
      (* i16 *)
      | TYPE_I 32, DV_Int (DI_I32 i1), TYPE_I 16 =>
          Some (DV_Int (DI_I16 (repr (unsigned i1))))
      | TYPE_I 64, DV_Int (DI_I64 i1), TYPE_I 16 =>
          Some (DV_Int (DI_I16 (repr (unsigned i1))))
      (* i32 *)
      | TYPE_I 64, DV_Int (DI_I64 i1), TYPE_I 32 =>
          Some (DV_Int (DI_I32 (repr (unsigned i1))))
      | _, DV_Poison _, t => Some (DV_Poison t)
      | _, _, _ => None
      end
  | Bitcast =>
      match t1, x, t2 with
      | TYPE_I bits1, x, TYPE_I bits2 =>
          if (bits1 =? bits2)%positive then Some x else None
      | _, _, _ => None
      end
  end
.
