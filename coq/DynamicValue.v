From SE Require Import BitVectors.

Inductive dynamic_value : Type :=
  | DV_I1 (x : int1)
  | DV_I8 (x : int8)
  | DV_I16 (x : int16)
  | DV_I32 (x : int32)
  | DV_I64 (x : int64)
.
