Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2387577 : forall m : int, forall n : int, @COND Prop (n = (int_of_num (NUMERAL 0))) (((div m n) = (int_of_num (NUMERAL 0))) /\ ((rem m n) = m)) ((int_le (int_of_num (NUMERAL 0)) (rem m n)) /\ ((int_lt (rem m n) (int_abs n)) /\ (m = (int_add (int_mul (div m n) n) (rem m n))))).
