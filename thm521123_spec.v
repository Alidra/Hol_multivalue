Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem521123 : forall (n : nat) (m : nat), ~ ((Peano.le m n) /\ (Peano.lt n m)).