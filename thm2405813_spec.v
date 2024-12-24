Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2405813 : forall (m : nat), ((int_add (int_neg (int_of_num m)) (int_of_num m)) = (int_of_num (NUMERAL 0))) /\ ((int_add (int_of_num m) (int_neg (int_of_num m))) = (int_of_num (NUMERAL 0))).
