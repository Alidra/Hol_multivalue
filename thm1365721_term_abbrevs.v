Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := ((real_lt (real_of_num x0) (real_of_num x1)) = (Peano.lt x0 x1)) /\ (((real_lt (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.lt x1 x0)) /\ ((real_lt (real_neg (real_of_num x0)) (real_of_num x1)) = (~ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))))).
