From Coq Require Import Bool.
From Coq Require Import Lia.
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

  (* Lemmas *)
  add_commut : forall x y : I, add x y = add y x;
  add_assoc : forall x y z : I, add (add x y) z = add x (add y z);
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

  (* Lemmas *)
  add_commut := Int1.add_commut;
  add_assoc := Int1.add_assoc;
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

  (* Lemmas *)
  add_commut := Int8.add_commut;
  add_assoc := Int8.add_assoc;
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

  (* Lemmas *)
  add_commut := Int16.add_commut;
  add_assoc := Int16.add_assoc;
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

  (* Lemmas *)
  add_commut := Int32.add_commut;
  add_assoc := Int32.add_assoc;
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

  (* Lemmas *)
  add_commut := Int64.add_commut;
  add_assoc := Int64.add_assoc;
}.

Definition di_is_const (di : dynamic_int) (n : Z) : bool :=
  match di with
  | DI_I1 x => eq x (repr n)
  | DI_I8 x => eq x (repr n)
  | DI_I16 x => eq x (repr n)
  | DI_I32 x => eq x (repr n)
  | DI_I64 x => eq x (repr n)
  end
.

Definition di_unsigned (di : dynamic_int) : Z :=
  match di with
  | DI_I1 n => unsigned n
  | DI_I8 n => unsigned n
  | DI_I16 n => unsigned n
  | DI_I32 n => unsigned n
  | DI_I64 n => unsigned n
  end
.

Lemma int1_eqb_eq : forall (x y : Int1.int),
  Int1.eq x y = true -> x = y.
Proof.
  intros x y H.
  pose proof (Int1.eq_spec x y) as L.
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
  intros n.
  destruct n as [x Hr].
  destruct (x =? 0)%Z eqn:E.
  {
    rewrite Z.eqb_eq in E.
    left.
    apply Int1.mkint_eq.
    subst.
    reflexivity.
  }
  {
    rewrite Z.eqb_neq in E.
    unfold Int1.modulus, Int1.wordsize, Wordsize_1.wordsize, two_power_nat in Hr.
    simpl in Hr.
    assert(L : (x = 1)%Z).
    { lia. }
    right.
    apply Int1.mkint_eq.
    subst.
    reflexivity.
  }
Qed.

Lemma int1_and_one_right : forall (n : Int1.int),
  and n one = n.
Proof.
  intros n.
  replace one with Int1.mone.
  { apply Int1.and_mone. }
  { apply int1_eqb_eq. reflexivity. }
Qed.

Lemma int1_and_one_left : forall (n : Int1.int),
  and one n = n.
Proof.
  intros n.
  replace one with Int1.mone.
  { apply Int1.and_mone_l. }
  { apply int1_eqb_eq. reflexivity. }
Qed.

Lemma int1_and_one_infer_left : forall (n1 n2 : Int1.int),
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

Lemma int1_and_one_infer_right : forall (n1 n2 : Int1.int),
  Int1.and n1 n2 = Int1.one -> n2 = Int1.one.
Proof.
  intros n1 n2 H.
  assert(L: n2 = Int1.zero \/ n2 = Int1.one).
  { apply int1_destruct. }
  destruct L as [L | L].
  {
    rewrite L in H.
    rewrite Int1.and_zero in H.
    discriminate H.
  }
  { assumption. }
Qed.

Lemma int1_lt_one : forall (n : Int1.int),
  (Int1.unsigned n >=? 1)%Z = false -> n = Int1.zero.
Proof.
  intros n H.
  assert(L: n = Int1.zero \/ n = Int1.one).
  { apply int1_destruct. }
  destruct L.
  { assumption. }
  { subst. simpl in H. discriminate H. }
Qed.

Lemma int1_or_one_left : forall (n : Int1.int),
  Int1.or Int1.one n = Int1.one.
Proof.
  intros n.
  assert(L: n = Int1.zero \/ n = Int1.one).
  { apply int1_destruct. }
  destruct L; subst; reflexivity.
Qed.

Lemma int1_or_one_right : forall (n : Int1.int),
  Int1.or n Int1.one = Int1.one.
Proof.
  intros n.
  assert(L: n = Int1.zero \/ n = Int1.one).
  { apply int1_destruct. }
  destruct L; subst; reflexivity.
Qed.

(* TODO: rename? *)
Lemma ltu_zext_i1_i64 : forall n,
  (Int1.ltu n (Int1.repr 1)) =
  (Int64.ltu (Integers.Int64.repr (Int1.unsigned n)) (Integers.Int64.repr 1)).
Proof.
  intros n.
  destruct n as [x Hx].
  unfold Int1.ltu.
  unfold Int64.ltu.
  simpl.
  rewrite (Int64.unsigned_repr_eq).
  rewrite Zmod_small.
  { reflexivity. }
  {
    unfold Int1.modulus, Int1.wordsize, two_power_nat in Hx.
    simpl in Hx.
    unfold Int64.modulus, Int64.wordsize, two_power_nat.
    simpl.
    lia.
  }
Qed.

(* TODO: rename *)
Lemma eq_zero_zext_i1_i64 : forall n : int1,
  Int1.eq n Int1.zero = Int64.eq (Int64.repr (Int1.unsigned n)) Int64.zero.
Proof.
  intro n.
  apply eq_true_iff_eq.
  split; intros Heq.
  {
    apply int1_eqb_eq in Heq.
    subst.
    reflexivity.
  }
  {
    destruct n as [x Hx].
    simpl in Heq.
    unfold Int64.eq in Heq.
    replace (Int64.unsigned Int64.zero)%Z with 0%Z in Heq; try reflexivity.
    rewrite (Int64.unsigned_repr_eq) in Heq.
    replace (x mod Int64.modulus)%Z with x in Heq.
    {
      destruct (Coqlib.zeq x 0) as [H | H] eqn:E; try inversion Heq.
      subst.
      reflexivity.
    }
    {
      symmetry.
      apply Zmod_small.
      unfold Int64.modulus, Int64.wordsize, two_power_nat.
      unfold Int1.modulus, Int1.wordsize, two_power_nat in Hx.
      simpl.
      simpl in Hx.
      lia.
    }
  }
Qed.

Lemma int8_eqb_eq : forall (x y : Int8.int),
  Int8.eq x y = true -> x = y.
Proof.
  intros x y H.
  pose proof (Int8.eq_spec x y) as L.
  rewrite H in L.
  assumption.
Qed.

(* TODO: rename *)
Lemma eq_zero_zext_i8_i64 : forall n : int8,
  Int8.eq n Int8.zero = Int64.eq (Int64.repr (Int8.unsigned n)) Int64.zero.
Proof.
  intro n.
  apply eq_true_iff_eq.
  split; intros Heq.
  {
    apply int8_eqb_eq in Heq.
    subst.
    reflexivity.
  }
  {
    destruct n as [x Hx].
    simpl in Heq.
    unfold Int64.eq in Heq.
    replace (Int64.unsigned Int64.zero)%Z with 0%Z in Heq; try reflexivity.
    rewrite (Int64.unsigned_repr_eq) in Heq.
    replace (x mod Int64.modulus)%Z with x in Heq.
    {
      destruct (Coqlib.zeq x 0) as [H | H] eqn:E; try inversion Heq.
      subst.
      reflexivity.
    }
    {
      symmetry.
      apply Zmod_small.
      unfold Int64.modulus, Int64.wordsize, two_power_nat.
      unfold Int8.modulus, Int8.wordsize, two_power_nat in Hx.
      simpl.
      simpl in Hx.
      lia.
    }
  }
Qed.

(* TODO: rename? *)
Lemma ltu_zext_i8_i64 : forall n,
  (Int8.ltu n (Int8.repr 8)) =
  (Int64.ltu (Integers.Int64.repr (Int8.unsigned n)) (Integers.Int64.repr 8)).
Proof.
  intros n.
  destruct n as [x Hx].
  unfold Int8.ltu.
  unfold Int64.ltu.
  simpl.
  rewrite (Int64.unsigned_repr_eq).
  rewrite Zmod_small.
  { reflexivity. }
  {
    unfold Int8.modulus, Int8.wordsize, two_power_nat in Hx.
    simpl in Hx.
    unfold Int64.modulus, Int64.wordsize, two_power_nat.
    simpl.
    lia.
  }
Qed.

Lemma int16_eqb_eq : forall (x y : Int16.int),
  Int16.eq x y = true -> x = y.
Proof.
  intros x y H.
  pose proof (Int16.eq_spec x y) as L.
  rewrite H in L.
  assumption.
Qed.

(* TODO: rename *)
Lemma eq_zero_zext_i16_i64 : forall n : int16,
  Int16.eq n Int16.zero = Int64.eq (Int64.repr (Int16.unsigned n)) Int64.zero.
Proof.
  intro n.
  apply eq_true_iff_eq.
  split; intros Heq.
  {
    apply int16_eqb_eq in Heq.
    subst.
    reflexivity.
  }
  {
    destruct n as [x Hx].
    simpl in Heq.
    unfold Int64.eq in Heq.
    replace (Int64.unsigned Int64.zero)%Z with 0%Z in Heq; try reflexivity.
    rewrite (Int64.unsigned_repr_eq) in Heq.
    replace (x mod Int64.modulus)%Z with x in Heq.
    {
      destruct (Coqlib.zeq x 0) as [H | H] eqn:E; try inversion Heq.
      subst.
      reflexivity.
    }
    {
      symmetry.
      apply Zmod_small.
      unfold Int64.modulus, Int64.wordsize, two_power_nat.
      unfold Int16.modulus, Int16.wordsize, two_power_nat in Hx.
      simpl.
      simpl in Hx.
      lia.
    }
  }
Qed.

Lemma ltu_zext_i16_i64 : forall n,
  (Int16.ltu n (Int16.repr 16)) =
  (Int64.ltu (Integers.Int64.repr (Int16.unsigned n)) (Integers.Int64.repr 16)).
Proof.
  intros n.
  destruct n as [x Hx].
  unfold Int16.ltu.
  unfold Int64.ltu.
  simpl.
  rewrite (Int64.unsigned_repr_eq).
  rewrite Zmod_small.
  { reflexivity. }
  {
    unfold Int16.modulus, Int16.wordsize, two_power_nat in Hx.
    simpl in Hx.
    unfold Int64.modulus, Int64.wordsize, two_power_nat.
    simpl.
    lia.
  }
Qed.

Lemma int32_eqb_eq : forall (x y : Int32.int),
  Int32.eq x y = true -> x = y.
Proof.
  intros x y H.
  assert(L : if Int32.eq x y then x = y else x <> y).
  { apply Int32.eq_spec. }
  rewrite H in L.
  assumption.
Qed.

Lemma int32_sub_add : forall (n1 n2 : int32),
  sub n1 n2 = add n1 (repr (unsigned (sub zero n2))).
Proof.
  intros n1 n2.
  rewrite Int32.repr_unsigned.
  rewrite Int.sub_zero_r.
  apply Int32.sub_add_opp.
Qed.

(* TODO: rename *)
Lemma eq_zero_zext_i32_i64 : forall n : int32,
  Int32.eq n Int32.zero = Int64.eq (Int64.repr (Int32.unsigned n)) Int64.zero.
Proof.
  intro n.
  apply eq_true_iff_eq.
  split; intros Heq.
  {
    apply int32_eqb_eq in Heq.
    subst.
    reflexivity.
  }
  {
    destruct n as [x Hx].
    simpl in Heq.
    unfold Int64.eq in Heq.
    replace (Int64.unsigned Int64.zero)%Z with 0%Z in Heq; try reflexivity.
    rewrite (Int64.unsigned_repr_eq) in Heq.
    replace (x mod Int64.modulus)%Z with x in Heq.
    {
      destruct (Coqlib.zeq x 0) as [H | H] eqn:E; try inversion Heq.
      subst.
      reflexivity.
    }
    {
      symmetry.
      apply Zmod_small.
      unfold Int64.modulus, Int64.wordsize, two_power_nat.
      unfold Int32.modulus, Int32.wordsize, two_power_nat in Hx.
      simpl.
      simpl in Hx.
      lia.
    }
  }
Qed.

(* TODO: rename? *)
Lemma ltu_zext_i32_i64 : forall n,
  (Int32.ltu n (Int32.repr 32)) =
  (Int64.ltu (Integers.Int64.repr (Int32.unsigned n)) (Integers.Int64.repr 32)).
Proof.
  intros n.
  destruct n as [x Hx].
  unfold Int32.ltu.
  unfold Int64.ltu.
  simpl.
  rewrite (Int64.unsigned_repr_eq).
  rewrite Zmod_small.
  { reflexivity. }
  {
    unfold Int32.modulus, Int32.wordsize, two_power_nat in Hx.
    simpl in Hx.
    unfold Int64.modulus, Int64.wordsize, two_power_nat.
    simpl.
    lia.
  }
Qed.
