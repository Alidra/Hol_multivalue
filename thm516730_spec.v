Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516730 : forall (n : nat), (fun n' : nat => (BIT0 n') = (Nat.add n' n')) n.