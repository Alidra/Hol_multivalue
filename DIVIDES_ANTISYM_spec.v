Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3108438 : forall m : nat, forall n : nat, ((num_divides m n) /\ (num_divides n m)) = (m = n).
