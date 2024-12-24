Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516842 : forall (m : nat) (n : nat), (fun n' : nat => ((S m) = (S n')) = (m = n')) n.
