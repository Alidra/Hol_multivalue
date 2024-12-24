Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1630283 : forall x : real, forall n : nat, ((real_pow x n) = (real_of_num (NUMERAL 0))) = ((x = (real_of_num (NUMERAL 0))) /\ (~ (n = (NUMERAL 0)))).
