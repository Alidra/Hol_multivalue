Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1988318 : forall (x : real) (y : real), (~ (x = y)) = ((real_gt (real_sub x y) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x y)) (real_of_num (NUMERAL 0)))).
