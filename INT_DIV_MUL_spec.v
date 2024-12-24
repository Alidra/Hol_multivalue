Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2599937 : (forall m : int, forall n : int, (~ (n = (int_of_num (NUMERAL 0)))) -> (div (int_mul m n) n) = m) /\ (forall m : int, forall n : int, (~ (m = (int_of_num (NUMERAL 0)))) -> (div (int_mul m n) m) = n).
