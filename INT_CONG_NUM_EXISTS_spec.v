Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3130395 : forall x : int, forall y : int, ((y = (int_of_num (NUMERAL 0))) -> int_le (int_of_num (NUMERAL 0)) x) -> exists n : nat, @eq2 int (int_of_num n) x (int_mod y).
