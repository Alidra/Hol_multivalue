Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) (x1 : int) (x2 : int) (x3 : nat) (x4 : int) (x5 : int) (x6 : int) (x7 : nat) := ((int_add x0 (int_add x1 x2)) = (int_add (int_add x0 x1) x2)) /\ (((int_mul (int_pow x6 x3) (int_pow x6 x7)) = (int_pow x6 (Nat.add x3 x7))) /\ (((int_mul x6 (int_pow x6 x7)) = (int_pow x6 (S x7))) /\ (((int_mul (int_pow x6 x7) x6) = (int_pow x6 (S x7))) /\ (((int_mul x6 x6) = (int_pow x6 (NUMERAL (BIT0 (BIT1 0))))) /\ (((int_pow (int_mul x6 x4) x7) = (int_mul (int_pow x6 x7) (int_pow x4 x7))) /\ (((int_pow (int_pow x6 x3) x7) = (int_pow x6 (Nat.mul x3 x7))) /\ (((int_pow x6 (NUMERAL 0)) = (int_of_num (NUMERAL (BIT1 0)))) /\ (((int_pow x6 (NUMERAL (BIT1 0))) = x6) /\ (((int_mul x6 (int_add x4 x5)) = (int_add (int_mul x6 x4) (int_mul x6 x5))) /\ ((int_pow x6 (S x7)) = (int_mul x6 (int_pow x6 x7)))))))))))).
