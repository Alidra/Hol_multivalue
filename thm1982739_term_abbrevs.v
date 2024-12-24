Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul x0 (real_mul x1 (real_mul x2 x3)).
Definition term0 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_mul x0 x1) (real_mul x2 x3).
