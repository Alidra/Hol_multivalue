Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : real) (x1 : real) := real_add x1 (real_mul x0 x1).
Definition term1 (x0 : real) (x1 : real) := real_mul (real_add x0 (real_of_num (NUMERAL (BIT1 0)))) x1.
