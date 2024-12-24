Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3116350 : forall (n : nat) (m : nat), ((fun n' : nat => (m = n') = ((num_divides m n') /\ (num_divides n' m))) n) = ((m = n) = ((num_divides m n) /\ (num_divides n m))).
