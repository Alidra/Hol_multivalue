Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1630835 : forall w : real, forall x : real, forall y : real, forall z : real, ((real_le (real_of_num (NUMERAL 0)) w) /\ ((real_lt w x) /\ ((real_le (real_of_num (NUMERAL 0)) y) /\ (real_lt y z)))) -> real_lt (real_mul w y) (real_mul x z).
