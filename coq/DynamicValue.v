(* TODO: rename module/type? *)
From Coq Require Import ZArith.

From SE Require Import BitVectors.
From SE.Numeric Require Import Integers.
From SE Require Import LLVMAst.

Inductive dynamic_value : Type :=
  | DV_I1 (x : int1)
  | DV_I8 (x : int8)
  | DV_I16 (x : int16)
  | DV_I32 (x : int32)
  | DV_I64 (x : int64)
  | DV_Undef
  | DV_Poison
.

Class VInt I : Type := {
  (* Comparisons *)
  eq : I -> I -> bool;
  cmp : comparison -> I -> I -> bool;
  cmpu : comparison -> I -> I -> bool;

  (* Constants *)
  bitwidth : nat;
  zero : I;
  one : I;

  (* Arithmetic *)
  add : I -> I -> I;
  add_carry : I -> I -> I -> I;
  add_overflow : I -> I -> I -> I;

  sub : I -> I -> I;
  sub_borrow : I -> I -> I -> I;
  sub_overflow : I -> I -> I -> I;

  mul : I -> I -> I;

  divu : I -> I -> I;
  divs : I -> I -> I;
  modu : I -> I -> I;
  mods : I -> I -> I;

  shl : I -> I -> I;
  shr : I -> I -> I;
  shru : I -> I -> I;

  negative : I -> I;

  (* Logic *)
  and : I -> I -> I;
  or : I -> I -> I;
  xor : I -> I -> I;

  (* Bounds *)
  min_signed : Z;
  max_signed : Z;

  (* Conversion *)
  to_dvalue : I -> dynamic_value;
  unsigned : I -> Z;
  signed : I -> Z;

  repr : Z -> I;
}.

Global Instance VInt1 : VInt Int1.int := {
  (* Comparisons *)
  eq := Int1.eq;
  cmp := Int1.cmp;
  cmpu := Int1.cmpu;

  bitwidth := 1;

  (* Constants *)
  zero := Int1.zero;
  one := Int1.one;

  (* Arithmetic *)
  add := Int1.add;
  add_carry := Int1.add_carry;
  add_overflow := Int1.add_overflow;

  sub := Int1.sub;
  sub_borrow := Int1.sub_borrow;
  sub_overflow := Int1.sub_overflow;

  mul := Int1.mul;

  divu := Int1.divu;
  divs := Int1.divs;
  modu := Int1.modu;
  mods := Int1.mods;

  shl := Int1.shl;
  shr := Int1.shr;
  shru := Int1.shru;

  negative := Int1.negative;

  (* Logic *)
  and := Int1.and;
  or := Int1.or;
  xor := Int1.xor;

  (* Bounds *)
  min_signed := Int1.min_signed;
  max_signed := Int1.max_signed;

  (* Conversion *)
  to_dvalue := DV_I1;
  unsigned := Int1.unsigned;
  signed := Int1.signed;

  repr := Int1.repr;
}.

Global Instance VInt8 : VInt Int8.int := {
  (* Comparisons *)
  eq := Int8.eq;
  cmp := Int8.cmp;
  cmpu := Int8.cmpu;

  bitwidth := 8;

  (* Constants *)
  zero := Int8.zero;
  one := Int8.one;

  (* Arithmetic *)
  add := Int8.add;
  add_carry := Int8.add_carry;
  add_overflow := Int8.add_overflow;

  sub := Int8.sub;
  sub_borrow := Int8.sub_borrow;
  sub_overflow := Int8.sub_overflow;

  mul := Int8.mul;

  divu := Int8.divu;
  divs := Int8.divs;
  modu := Int8.modu;
  mods := Int8.mods;

  shl := Int8.shl;
  shr := Int8.shr;
  shru := Int8.shru;

  negative := Int8.negative;

  (* Logic *)
  and := Int8.and;
  or := Int8.or;
  xor := Int8.xor;

  (* Bounds *)
  min_signed := Int8.min_signed;
  max_signed := Int8.max_signed;

  (* Conversion *)
  to_dvalue := DV_I8;
  unsigned := Int8.unsigned;
  signed := Int8.signed;

  repr := Int8.repr;
}.

Global Instance VInt16 : VInt Int16.int := {
  (* Comparisons *)
  eq := Int16.eq;
  cmp := Int16.cmp;
  cmpu := Int16.cmpu;

  bitwidth := 16;

  (* Constants *)
  zero := Int16.zero;
  one := Int16.one;

  (* Arithmetic *)
  add := Int16.add;
  add_carry := Int16.add_carry;
  add_overflow := Int16.add_overflow;

  sub := Int16.sub;
  sub_borrow := Int16.sub_borrow;
  sub_overflow := Int16.sub_overflow;

  mul := Int16.mul;

  divu := Int16.divu;
  divs := Int16.divs;
  modu := Int16.modu;
  mods := Int16.mods;

  shl := Int16.shl;
  shr := Int16.shr;
  shru := Int16.shru;

  negative := Int16.negative;

  (* Logic *)
  and := Int16.and;
  or := Int16.or;
  xor := Int16.xor;

  (* Bounds *)
  min_signed := Int16.min_signed;
  max_signed := Int16.max_signed;

  (* Conversion *)
  to_dvalue := DV_I16;
  unsigned := Int16.unsigned;
  signed := Int16.signed;

  repr := Int16.repr;
}.

Global Instance VInt32 : VInt Int32.int := {
  (* Comparisons *)
  eq := Int32.eq;
  cmp := Int32.cmp;
  cmpu := Int32.cmpu;

  bitwidth := 32;

  (* Constants *)
  zero := Int32.zero;
  one := Int32.one;

  (* Arithmetic *)
  add := Int32.add;
  add_carry := Int32.add_carry;
  add_overflow := Int32.add_overflow;

  sub := Int32.sub;
  sub_borrow := Int32.sub_borrow;
  sub_overflow := Int32.sub_overflow;

  mul := Int32.mul;

  divu := Int32.divu;
  divs := Int32.divs;
  modu := Int32.modu;
  mods := Int32.mods;

  shl := Int32.shl;
  shr := Int32.shr;
  shru := Int32.shru;

  negative := Int32.negative;

  (* Logic *)
  and := Int32.and;
  or := Int32.or;
  xor := Int32.xor;

  (* Bounds *)
  min_signed := Int32.min_signed;
  max_signed := Int32.max_signed;

  (* Conversion *)
  to_dvalue := DV_I32;
  unsigned := Int32.unsigned;
  signed := Int32.signed;

  repr := Int32.repr;
}.

Global Instance VInt64 : VInt Int64.int := {
  (* Comparisons *)
  eq := Int64.eq;
  cmp := Int64.cmp;
  cmpu := Int64.cmpu;

  bitwidth := 64;

  (* Constants *)
  zero := Int64.zero;
  one := Int64.one;

  (* Arithmetic *)
  add := Int64.add;
  add_carry := Int64.add_carry;
  add_overflow := Int64.add_overflow;

  sub := Int64.sub;
  sub_borrow := Int64.sub_borrow;
  sub_overflow := Int64.sub_overflow;

  mul := Int64.mul;

  divu := Int64.divu;
  divs := Int64.divs;
  modu := Int64.modu;
  mods := Int64.mods;

  shl := Int64.shl;
  shr := Int64.shr;
  shru := Int64.shru;

  negative := Int64.negative;

  (* Logic *)
  and := Int64.and;
  or := Int64.or;
  xor := Int64.xor;

  (* Bounds *)
  min_signed := Int64.min_signed;
  max_signed := Int64.max_signed;

  (* Conversion *)
  to_dvalue := DV_I64;
  unsigned := Int64.unsigned;
  signed := Int64.signed;

  repr := Int64.repr;
}.

(* TODO: compare with the latest version *)
(* TODO: why returns DV_Undef in some cases? *)
Definition eval_ibinop_generic {Int} `{VInt Int} (op : ibinop) (x y : Int) : dynamic_value :=
  match op with
  | Add nuw nsw =>
    if orb (andb nuw (eq (add_carry x y zero) one))
           (andb nsw (eq (add_overflow x y zero) one)) then
      DV_Poison
    else
      to_dvalue (add x y)

  | Sub nuw nsw =>
    if orb (andb nuw (eq (sub_borrow x y zero) one))
           (andb nsw (eq (sub_overflow x y zero) one)) then
      DV_Poison
    else
      to_dvalue (sub x y)

  | Mul nuw nsw =>
    if (bitwidth =? 1)%nat then
      to_dvalue (mul x y)
    else
      let res := mul x y in
      let res_s' := ((signed x) * (signed y))%Z in
      if orb (andb nuw ((unsigned x) * (unsigned y) >? unsigned res)%Z)
             (andb nsw (orb (min_signed >? res_s')%Z (res_s' >? max_signed)%Z)) then
        DV_Poison
      else
        to_dvalue res

  | Shl nuw nsw =>
    if (bitwidth =? 1)%nat then
      if ((unsigned y) >=? 1)%Z then DV_Undef else to_dvalue x
    else
      let bz := Z.of_nat bitwidth in
      let res := shl x y in
      let res_u := unsigned res in
      let res_u' := Z.shiftl (unsigned x) (unsigned y) in
      if ((unsigned y) >=? bz)%Z then
        DV_Undef
      else if orb (andb nuw (res_u' >? res_u)%Z)
                  (andb nsw (negb (Z.shiftr (unsigned x) (bz - unsigned y) =? ((unsigned (negative res)) * (Z.pow 2 (unsigned y) - 1)))%Z)) then
        DV_Poison
      else
        to_dvalue res

  | UDiv ex =>
    if andb ex (negb ((unsigned x) mod (unsigned y) =? 0)%Z) then
      DV_Poison
    else
      to_dvalue (divu x y)

  | SDiv ex =>
    if andb ex (negb (((signed x) mod (signed y)) =? 0)%Z) then
      DV_Poison
    else
      to_dvalue (divs x y)

  | LShr ex =>
    if (bitwidth =? 1)%nat then
      if ((unsigned y) >=? 1)%Z then DV_Undef else to_dvalue x
    else
      let bz := Z.of_nat bitwidth in
      if ((unsigned y) >=? bz)%Z then
        DV_Undef
      else if andb ex (negb ((unsigned x) mod (Z.pow 2 (unsigned y)) =? 0)%Z) then
        DV_Poison
      else
        to_dvalue (shru x y)

  | AShr ex =>
    if (bitwidth =? 1)%nat then
      if ((unsigned y) >=? 1)%Z then DV_Undef else to_dvalue x
    else
      let bz := Z.of_nat bitwidth in
      if ((unsigned y) >=? bz)%Z then
        DV_Undef
      else if andb ex (negb ((unsigned x) mod (Z.pow 2 (unsigned y)) =? 0)%Z) then
       DV_Poison
     else
       to_dvalue (shr x y)

  | URem => to_dvalue (modu x y)

  | SRem => to_dvalue (mods x y)

  | And => to_dvalue (and x y)

  | Or => to_dvalue (or x y)

  | Xor => to_dvalue (xor x y)

  end
.

Definition make_bool (b : bool) : dynamic_value :=
  match b with
  | true => DV_I1 (Int1.repr 1)
  | false => DV_I1 (Int1.repr 0)
  end
.

Definition make_dv (bits : N) (n : Z) : option dynamic_value :=
  match bits with
  | 1%N => Some (DV_I1 (Int1.repr n))
  | 8%N => Some (DV_I8 (Int8.repr n))
  | 16%N => Some (DV_I16 (Int16.repr n))
  | 32%N => Some (DV_I32 (Int32.repr n))
  | 64%N => Some (DV_I64 (Int64.repr n))
  | _ => None
  end
.

Fixpoint eval_ibinop (op : ibinop) (v1 v2 : dynamic_value) : option dynamic_value :=
  match (v1, v2) with
  | (DV_I1 n1, DV_I1 n2)
  | (DV_I8 n1, DV_I8 n2)
  | (DV_I16 n1, DV_I16 n2)
  | (DV_I32 n1, DV_I32 n2)
  | (DV_I64 n1, DV_I64 n2) => Some (eval_ibinop_generic op n1 n2)
  | _ => None
  end
.

(* TODO: compare with the latest version *)
Definition eval_icmp_generic {Int} `{VInt Int} icmp (x y : Int) : dynamic_value :=
  if match icmp with
     | Eq => cmp Ceq x y
     | Ne => cmp Cne x y
     | Ugt => cmpu Cgt x y
     | Uge => cmpu Cge x y
     | Ult => cmpu Clt x y
     | Ule => cmpu Cle x y
     | Sgt => cmp Cgt x y
     | Sge => cmp Cge x y
     | Slt => cmp Clt x y
     | Sle => cmp Cle x y
     end
  then
    DV_I1 (Int1.one)
  else
    DV_I1 (Int1.zero)
.

Fixpoint eval_icmp (op : icmp) (v1 v2 : dynamic_value) : option dynamic_value :=
  match (v1, v2) with
  | (DV_I1 n1, DV_I1 n2)
  | (DV_I8 n1, DV_I8 n2)
  | (DV_I16 n1, DV_I16 n2)
  | (DV_I32 n1, DV_I32 n2)
  | (DV_I64 n1, DV_I64 n2) => Some (eval_icmp_generic op n1 n2)
  | _ => None
  end
.

(* TODO: compare with the latest version *)
(* TODO: handle i16 *)
Definition convert conv x t1 t2 : option dynamic_value :=
  match conv with
  | Trunc =>
    match t1, x, t2 with
    | TYPE_I 8, DV_I8 i1, TYPE_I 1 =>
      Some (DV_I1 (repr (unsigned i1)))
    | TYPE_I 32, DV_I32 i1, TYPE_I 1 =>
      Some (DV_I1 (repr (unsigned i1)))
    | TYPE_I 32, DV_I32 i1, TYPE_I 8 =>
      Some (DV_I8 (repr (unsigned i1)))
    | TYPE_I 64, DV_I64 i1, TYPE_I 1 =>
      Some (DV_I1 (repr (unsigned i1)))
    | TYPE_I 64, DV_I64 i1, TYPE_I 8 =>
      Some (DV_I8 (repr (unsigned i1)))
    | TYPE_I 64, DV_I64 i1, TYPE_I 32 =>
      Some (DV_I32 (repr (unsigned i1)))
    | _, _, _ => None
    end
  | Zext =>
    match t1, x, t2 with
    | TYPE_I 1, DV_I1 i1, TYPE_I 8 =>
      Some (DV_I8 (repr (unsigned i1)))
    | TYPE_I 1, DV_I1 i1, TYPE_I 32 =>
      Some (DV_I32 (repr (unsigned i1)))
    | TYPE_I 1, DV_I1 i1, TYPE_I 64 =>
      Some (DV_I64 (repr (unsigned i1)))
    | TYPE_I 8, DV_I8 i1, TYPE_I 32 =>
      Some (DV_I32 (repr (unsigned i1)))
    | TYPE_I 8, DV_I8 i1, TYPE_I 64 =>
      Some (DV_I64 (repr (unsigned i1)))
    | TYPE_I 32, DV_I32 i1, TYPE_I 64 =>
      Some (DV_I64 (repr (unsigned i1)))
    | _, _, _ => None
    end
  | Sext =>
    match t1, x, t2 with
    | TYPE_I 1, DV_I1 i1, TYPE_I 8 =>
      Some (DV_I8 (repr (signed i1)))
    | TYPE_I 1, DV_I1 i1, TYPE_I 32 =>
      Some (DV_I32 (repr (signed i1)))
    | TYPE_I 1, DV_I1 i1, TYPE_I 64 =>
      Some (DV_I64 (repr (signed i1)))
    | TYPE_I 8, DV_I8 i1, TYPE_I 32 =>
      Some (DV_I32 (repr (signed i1)))
    | TYPE_I 8, DV_I8 i1, TYPE_I 64 =>
      Some (DV_I64 (repr (signed i1)))
    | TYPE_I 32, DV_I32 i1, TYPE_I 64 =>
      Some (DV_I64 (repr (signed i1)))
    | _, _, _ => None
    end
  | Bitcast =>
    match t1, x, t2 with
    | TYPE_I bits1, x, TYPE_I bits2 =>
      if (bits1 =? bits2)%N then Some x else None
    | _, _, _ => None
    end
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
