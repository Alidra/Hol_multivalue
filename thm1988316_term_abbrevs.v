Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : real) (x1 : real) := ((~ (real_ge x0 x1)) = (real_gt (real_sub x1 x0) (real_of_num (NUMERAL 0)))) /\ ((~ (x0 = x1)) = ((real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x0 x1)) (real_of_num (NUMERAL 0))))).
