Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2405528 : forall (x : nat), ((int_neg (int_of_num (NUMERAL 0))) = (int_of_num (NUMERAL 0))) /\ ((int_neg (int_neg (int_of_num x))) = (int_of_num x)).
