Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) (x1 : int) (x2 : int) (x3 : nat) := ((int_mul x2 (int_add x0 x1)) = (int_add (int_mul x2 x0) (int_mul x2 x1))) /\ ((int_pow x2 (S x3)) = (int_mul x2 (int_pow x2 x3))).
Definition term1 (x0 : int) (x1 : int) (x2 : int) (x3 : nat) := ((int_pow x2 (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))) /\ (((int_pow x2 (NUMERAL (BIT1 0))) = x2) /\ (((int_mul x2 (int_add x0 x1)) = (int_add (int_mul x2 x0) (int_mul x2 x1))) /\ ((int_pow x2 (S x3)) = (int_mul x2 (int_pow x2 x3))))).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := int_mul x0 (int_add x1 x2).
Definition term2 (x0 : int) (x1 : int) (x2 : int) (x3 : nat) := ((int_pow x2 (NUMERAL (BIT1 0))) = x2) /\ (((int_mul x2 (int_add x0 x1)) = (int_add (int_mul x2 x0) (int_mul x2 x1))) /\ ((int_pow x2 (S x3)) = (int_mul x2 (int_pow x2 x3)))).
Definition term0 (x0 : nat) (x1 : int) (x2 : int) (x3 : int) (x4 : nat) := ((int_pow (int_pow x3 x0) x4) = (int_pow x3 (Nat.mul x0 x4))) /\ (((int_pow x3 (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))) /\ (((int_pow x3 (NUMERAL (BIT1 0))) = x3) /\ (((int_mul x3 (int_add x1 x2)) = (int_add (int_mul x3 x1) (int_mul x3 x2))) /\ ((int_pow x3 (S x4)) = (int_mul x3 (int_pow x3 x4)))))).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := int_add (int_mul x1 x0) (int_mul x1 x2).
