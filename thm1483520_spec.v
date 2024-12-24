Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483520 : forall (x : real) (y : real), ((real_le x y) = (real_ge (real_sub y x) (real_of_num (NUMERAL 0)))) /\ (((real_gt x y) = (real_gt (real_sub x y) (real_of_num (NUMERAL 0)))) /\ (((real_ge x y) = (real_ge (real_sub x y) (real_of_num (NUMERAL 0)))) /\ (((x = y) = ((real_sub x y) = (real_of_num (NUMERAL 0)))) /\ (((~ (real_lt x y)) = (real_ge (real_sub x y) (real_of_num (NUMERAL 0)))) /\ (((~ (real_le x y)) = (real_gt (real_sub x y) (real_of_num (NUMERAL 0)))) /\ (((~ (real_gt x y)) = (real_ge (real_sub y x) (real_of_num (NUMERAL 0)))) /\ (((~ (real_ge x y)) = (real_gt (real_sub y x) (real_of_num (NUMERAL 0)))) /\ ((~ (x = y)) = ((real_gt (real_sub x y) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x y)) (real_of_num (NUMERAL 0)))))))))))).
