Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := ((int_lt (int_of_num x0) (int_of_num x1)) = (Peano.lt x0 x1)) /\ (((int_lt (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) = (Peano.lt x1 x0)) /\ ((int_lt (int_neg (int_of_num x0)) (int_of_num x1)) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))))).
