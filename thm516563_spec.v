Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516563 : forall (n : nat), ((fun n' : nat => (BIT1 n') = (S (Nat.add n' n'))) n) = ((BIT1 n) = (S (Nat.add n n))).