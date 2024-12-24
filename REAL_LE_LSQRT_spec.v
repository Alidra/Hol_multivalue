Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1959044 : forall x : real, forall y : real, ((real_le (real_of_num (NUMERAL 0)) y) /\ (real_le x (real_pow y (NUMERAL (BIT0 (BIT1 0)))))) -> real_le (sqrt x) y.
