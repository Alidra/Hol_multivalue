Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308850 : forall x : int, forall n : nat, (~ (x = (int_of_num (NUMERAL 0)))) -> ~ ((int_pow x n) = (int_of_num (NUMERAL 0))).
