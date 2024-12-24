Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2651667 : forall m : int, forall n : int, ((int_le (int_of_num (NUMERAL 0)) m) /\ (int_le (int_of_num (NUMERAL 0)) n)) -> int_le (int_of_num (NUMERAL 0)) (div m n).
