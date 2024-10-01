From Coq Require Import ZArith.

From SE.Numeric Require Import Integers.

Module Wordsize_1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof.
    unfold wordsize; congruence.
  Qed.
End Wordsize_1.

Module Int1 := Make(Wordsize_1).
Module Int8 := Byte.
Module Int32 := Int.

Definition int1 := Int1.int.
Definition int8 := Int8.int.
Definition int16 := Int16.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.

Inductive dynamic_int : Type :=
  | DI_I1 (n : int1)
  | DI_I8 (n : int8)
  | DI_I16 (n : int16)
  | DI_I32 (n : int32)
  | DI_I64 (n : int64)
.

Definition di_true := DI_I1 (Int1.repr 1%Z).
Definition di_false := DI_I1 (Int1.repr 0%Z).

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
  to_dint : I -> dynamic_int;
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
  to_dint := DI_I1;
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
  to_dint := DI_I8;
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
  to_dint := DI_I16;
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
  to_dint := DI_I32;
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
  to_dint := DI_I64;
  unsigned := Int64.unsigned;
  signed := Int64.signed;

  repr := Int64.repr;
}.

Lemma int1_eqb_eq : forall (x y : Int1.int),
  Int1.eq x y = true -> x = y.
Proof.
  intros x y H.
  assert(L : if Int1.eq x y then x = y else x <> y).
  { apply Int1.eq_spec. }
  rewrite H in L.
  assumption.
Qed.

Lemma int1_eqb_ne : forall (x y : Int1.int),
  Int1.eq x y = false -> x <> y.
Proof.
  intros x y H.
  assert(L : if Int1.eq x y then x = y else x <> y).
  { apply Int1.eq_spec. }
  rewrite H in L.
  assumption.
Qed.

Lemma int1_destruct : forall (n : Int1.int),
  n = Int1.zero \/ n = Int1.one.
Proof.
Admitted.

(* TOOD: rename to int1_and_one_l *)
Lemma int1_and_one : forall (n1 n2 : Int1.int),
  Int1.and n1 n2 = Int1.one -> n1 = Int1.one.
Proof.
  intros n1 n2 H.
  assert(L: n1 = Int1.zero \/ n1 = Int1.one).
  { apply int1_destruct. }
  destruct L as [L | L].
  {
    rewrite L in H.
    rewrite Int1.and_commut in H.
    rewrite Int1.and_zero in H.
    discriminate H.
  }
  { assumption. }
Qed.

Lemma int32_sub_add : forall (n1 n2 : int32),
  sub n1 n2 = add n1 (repr (unsigned (sub zero n2))).
Proof.
Admitted.
