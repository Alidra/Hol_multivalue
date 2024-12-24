Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) (x1 : int) (x2 : int) (x3 : int) (x4 : nat) (x5 : int) (x6 : int) (x7 : int) (x8 : nat) := ((int_add x1 (int_add x2 x3)) = (int_add x2 (int_add x1 x3))) /\ (((int_add (int_add x1 x0) x2) = (int_add (int_add x1 x2) x0)) /\ (((int_add x1 x2) = (int_add x2 x1)) /\ (((int_add x1 (int_add x2 x3)) = (int_add (int_add x1 x2) x3)) /\ (((int_mul (int_pow x7 x4) (int_pow x7 x8)) = (int_pow x7 (Nat.add x4 x8))) /\ (((int_mul x7 (int_pow x7 x8)) = (int_pow x7 (S x8))) /\ (((int_mul (int_pow x7 x8) x7) = (int_pow x7 (S x8))) /\ (((int_mul x7 x7) = (int_pow x7 (NUMERAL (BIT0 (BIT1 0))))) /\ (((int_pow (int_mul x7 x5) x8) = (int_mul (int_pow x7 x8) (int_pow x5 x8))) /\ (((int_pow (int_pow x7 x4) x8) = (int_pow x7 (Nat.mul x4 x8))) /\ (((int_pow x7 (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))) /\ (((int_pow x7 (NUMERAL (BIT1 0))) = x7) /\ (((int_mul x7 (int_add x5 x6)) = (int_add (int_mul x7 x5) (int_mul x7 x6))) /\ ((int_pow x7 (S x8)) = (int_mul x7 (int_pow x7 x8))))))))))))))).
