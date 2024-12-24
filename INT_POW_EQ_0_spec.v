Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307872 : forall x : int, forall n : nat, ((int_pow x n) = (int_of_num (NUMERAL 0))) = ((x = (int_of_num (NUMERAL 0))) /\ (~ (n = (NUMERAL 0)))).
