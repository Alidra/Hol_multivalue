Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416533 : forall (a : int), (int_mul a (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0)).
