From Coq Require Import List.
From Coq Require Import String.

Import ListNotations.

(* TODO: define as an axiom? *)
Lemma choice_axiom : forall (syms : list string), exists sym, ~ In sym syms.
Proof.
Admitted.
