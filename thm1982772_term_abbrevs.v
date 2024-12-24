Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : real) (x2 : real) (x3 : real) (x4 : nat) := ((real_pow (real_pow x3 x0) x4) = (real_pow x3 (Nat.mul x0 x4))) /\ (((real_pow x3 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (((real_pow x3 (NUMERAL (BIT1 0))) = x3) /\ (((real_mul x3 (real_add x1 x2)) = (real_add (real_mul x3 x1) (real_mul x3 x2))) /\ ((real_pow x3 (S x4)) = (real_mul x3 (real_pow x3 x4)))))).
