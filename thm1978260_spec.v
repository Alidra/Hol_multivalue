Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1978260 : forall (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : (real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_of_num (NUMERAL 0)) y2)), (real_add (real_div x1 y1) (real_div x2 y2)) = (real_mul (real_add (real_mul x1 y2) (real_mul x2 y1)) (real_mul (real_inv y1) (real_inv y2))).