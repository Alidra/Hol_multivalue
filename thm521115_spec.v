Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem521115 : forall (n : nat) (m : nat), ~ ((Peano.lt m n) /\ (Peano.le n m)).
