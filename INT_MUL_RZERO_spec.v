Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306290 : forall x : int, (int_mul x (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0)).
