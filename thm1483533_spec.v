Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483533 : forall (x : real) (y : real), (~ (real_le x y)) = (real_gt (real_sub x y) (real_of_num (NUMERAL 0))).
