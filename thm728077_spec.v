Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem728077 : forall (n : nat), (fun n' : nat => (S (BIT0 n')) = (BIT1 n')) n.