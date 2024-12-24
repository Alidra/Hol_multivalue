Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : int) (x2 : int) (x3 : int) (x4 : nat) := ((int_mul x3 x3) = (int_pow x3 (NUMERAL (BIT0 (BIT1 0))))) /\ (((int_pow (int_mul x3 x1) x4) = (int_mul (int_pow x3 x4) (int_pow x1 x4))) /\ (((int_pow (int_pow x3 x0) x4) = (int_pow x3 (Nat.mul x0 x4))) /\ (((int_pow x3 (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))) /\ (((int_pow x3 (NUMERAL (BIT1 0))) = x3) /\ (((int_mul x3 (int_add x1 x2)) = (int_add (int_mul x3 x1) (int_mul x3 x2))) /\ ((int_pow x3 (S x4)) = (int_mul x3 (int_pow x3 x4)))))))).
