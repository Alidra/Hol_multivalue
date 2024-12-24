Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1900060 : forall x : real, forall y : real, ((real_le (real_of_num (NUMERAL 0)) y) /\ ((real_pow y (NUMERAL (BIT0 (BIT1 0)))) = x)) -> (sqrt x) = y.
