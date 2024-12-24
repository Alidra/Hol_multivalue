Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1594665 : forall x : real, forall y : real, ((real_div x y) = (real_of_num (NUMERAL (BIT1 0)))) = ((x = y) /\ ((~ (x = (real_of_num (NUMERAL 0)))) /\ (~ (y = (real_of_num (NUMERAL 0)))))).
