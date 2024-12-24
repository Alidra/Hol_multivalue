Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2526537 : forall m : int, forall n : int, ((rem m n) = (int_of_num (NUMERAL 0))) = (int_divides n m).
