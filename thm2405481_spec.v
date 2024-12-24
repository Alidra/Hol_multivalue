Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2405481 : forall (m : nat) (n : nat), (((int_of_num m) = (int_of_num n)) = (m = n)) /\ ((((int_neg (int_of_num m)) = (int_neg (int_of_num n))) = (m = n)) /\ ((((int_neg (int_of_num m)) = (int_of_num n)) = ((m = (NUMERAL 0)) /\ (n = (NUMERAL 0)))) /\ (((int_of_num m) = (int_neg (int_of_num n))) = ((m = (NUMERAL 0)) /\ (n = (NUMERAL 0)))))).
