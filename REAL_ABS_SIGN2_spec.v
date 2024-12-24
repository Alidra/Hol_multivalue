Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1542348 : forall x : real, forall y : real, (real_lt (real_abs (real_sub x y)) (real_neg y)) -> real_lt x (real_of_num (NUMERAL 0)).
