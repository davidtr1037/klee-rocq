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
