Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3110728 : forall n : nat, (num_divides n (NUMERAL (BIT1 0))) = (n = (NUMERAL (BIT1 0))).
