Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2301483 : forall x : int, forall y : int, ((int_mul x y) = (int_of_num (NUMERAL 0))) = ((x = (int_of_num (NUMERAL 0))) \/ (y = (int_of_num (NUMERAL 0)))).