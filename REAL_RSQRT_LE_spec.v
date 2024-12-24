Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1966798 : forall x : real, forall y : real, ((real_le (real_of_num (NUMERAL 0)) x) /\ ((real_le (real_of_num (NUMERAL 0)) y) /\ (real_le x (sqrt y)))) -> real_le (real_pow x (NUMERAL (BIT0 (BIT1 0)))) y.
