Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1988295 : forall (x : real) (y : real), (~ (real_lt x y)) = (real_ge (real_sub x y) (real_of_num (NUMERAL 0))).
