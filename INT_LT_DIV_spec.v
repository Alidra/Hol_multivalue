Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2657711 : forall m : int, forall n : int, ((int_lt (int_of_num (NUMERAL 0)) n) /\ (int_le n m)) -> int_lt (int_of_num (NUMERAL 0)) (div m n).