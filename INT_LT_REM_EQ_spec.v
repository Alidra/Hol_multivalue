Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2403542 : forall m : int, forall n : int, (int_lt (rem m n) n) = ((int_lt (int_of_num (NUMERAL 0)) n) \/ ((n = (int_of_num (NUMERAL 0))) /\ (int_lt m (int_of_num (NUMERAL 0))))).
