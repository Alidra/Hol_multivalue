Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303298 : forall x : int, int_le (int_of_num (NUMERAL 0)) (int_mul x x).
