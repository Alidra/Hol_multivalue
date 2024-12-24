Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_of_num (NUMERAL 0)) x3)) -> (real_add (real_div x0 x2) (real_div x1 x3)) = (real_mul (real_add (real_mul x0 x3) (real_mul x1 x2)) (real_mul (real_inv x2) (real_inv x3))).
Definition term1 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
