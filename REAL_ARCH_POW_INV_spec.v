Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1709542 : forall x : real, forall y : real, ((real_lt (real_of_num (NUMERAL 0)) y) /\ (real_lt x (real_of_num (NUMERAL (BIT1 0))))) -> exists n : nat, real_lt (real_pow x n) y.
