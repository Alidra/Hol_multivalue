Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2647681 : forall m : int, forall n : int, ((rem m n) = m) = ((n = (int_of_num (NUMERAL 0))) \/ ((int_le (int_of_num (NUMERAL 0)) m) /\ (int_lt m (int_abs n)))).
