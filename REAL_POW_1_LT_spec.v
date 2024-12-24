Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1638553 : forall n : nat, forall x : real, ((~ (n = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x) /\ (real_lt x (real_of_num (NUMERAL (BIT1 0)))))) -> real_lt (real_pow x n) (real_of_num (NUMERAL (BIT1 0))).
