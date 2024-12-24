Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3179842 : forall x : real, forall n : int, ((real_zpow x n) = (real_of_num (NUMERAL 0))) = ((x = (real_of_num (NUMERAL 0))) /\ (~ (n = (int_of_num (NUMERAL 0))))).
