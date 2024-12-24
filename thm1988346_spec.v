Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1988346 : forall (x : real) (y : real), (((real_gt x (real_of_num (NUMERAL 0))) /\ (y = (real_of_num (NUMERAL 0)))) -> real_gt (real_add x y) (real_of_num (NUMERAL 0))) /\ ((((real_gt x (real_of_num (NUMERAL 0))) /\ (real_ge y (real_of_num (NUMERAL 0)))) -> real_gt (real_add x y) (real_of_num (NUMERAL 0))) /\ (((real_gt x (real_of_num (NUMERAL 0))) /\ (real_gt y (real_of_num (NUMERAL 0)))) -> real_gt (real_add x y) (real_of_num (NUMERAL 0)))).
