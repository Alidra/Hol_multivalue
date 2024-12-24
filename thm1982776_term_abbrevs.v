Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : real) (x1 : real) (x2 : real) (x3 : nat) := ((real_pow x2 (NUMERAL (BIT1 0))) = x2) /\ (((real_mul x2 (real_add x0 x1)) = (real_add (real_mul x2 x0) (real_mul x2 x1))) /\ ((real_pow x2 (S x3)) = (real_mul x2 (real_pow x2 x3)))).
