Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483535 : forall (y : real) (x : real), (~ (real_gt x y)) = (real_ge (real_sub y x) (real_of_num (NUMERAL 0))).
