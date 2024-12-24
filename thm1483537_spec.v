Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483537 : forall (y : real) (x : real), (~ (real_ge x y)) = (real_gt (real_sub y x) (real_of_num (NUMERAL 0))).
