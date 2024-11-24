From Coq Require Import List.

Import ListNotations.

From SE Require Import BitVectors.
From SE Require Import Concrete.
From SE Require Import DynamicValue.

Inductive store_has_no_poison : dv_store -> Prop :=
  | Store_Has_No_Poison : forall ls,
      (forall x, (ls x) <> Some DV_Poison) ->
      store_has_no_poison ls
.

Inductive frame_has_no_poison : frame -> Prop :=
  | Frame_Has_No_Poison : forall ls ic pbid v,
      store_has_no_poison ls ->
      frame_has_no_poison (Frame ls ic pbid v)
.

Inductive stack_has_no_poison : list frame -> Prop :=
  | Stack_Has_No_Poison : forall stk,
      (forall f, In f stk -> frame_has_no_poison f) ->
      stack_has_no_poison stk
.

Inductive has_no_poison : state -> Prop :=
  | Has_No_Poison : forall ic c cs pbid ls stk gs mdl,
      store_has_no_poison ls ->
      store_has_no_poison gs ->
      stack_has_no_poison stk ->
      has_no_poison
        (mk_state
          ic
          c
          cs
          pbid
          ls
          stk
          gs
          mdl
        )
.

(* TODO: s1 should not contain poison? *)
Inductive ns_step : state -> state -> Prop :=
  | NS_Step : forall s1 s2,
      step s1 s2 -> has_no_poison s2 -> ns_step s1 s2
.
