Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem737643 : (forall n : nat, (S (BIT0 n)) = (BIT1 n)) /\ (forall n : nat, (S (BIT1 n)) = (BIT0 (S n))).