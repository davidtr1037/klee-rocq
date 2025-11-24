From Stdlib Require Import List.
From Stdlib Require Import String.

Import ListNotations.

(* TODO: use a more readable: fresh_name (n : nat) / extend_names (n : nat) *)

Definition fresh_name (l : list string) : string.
Admitted.

Definition extend_names (l : list string) : list string :=
  (fresh_name l) :: l.

Axiom fresh_name_lemma : forall l, ~ In (fresh_name l) l.
