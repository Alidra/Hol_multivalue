Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2389435 : forall m : int, forall n : int, (~ (n = (int_of_num (NUMERAL 0)))) -> (m = (int_add (int_mul (div m n) n) (rem m n))) /\ ((int_le (int_of_num (NUMERAL 0)) (rem m n)) /\ (int_lt (rem m n) (int_abs n))).
