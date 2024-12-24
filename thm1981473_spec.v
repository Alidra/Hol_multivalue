Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1981473 : forall (x1 : real) (y1 : real) (x2 : real) (y2 : real) (x3 : real) (y3 : real), (real_lt (real_of_num (NUMERAL 0)) y1) -> (real_lt (real_of_num (NUMERAL 0)) y2) -> (real_lt (real_of_num (NUMERAL 0)) y3) -> ((real_mul (real_add (real_mul x1 y2) (real_mul x2 y1)) y3) = (real_mul x3 (real_mul y1 y2))) -> (real_add (real_div x1 y1) (real_div x2 y2)) = (real_div x3 y3).
