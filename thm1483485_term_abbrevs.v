Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : real) (x1 : real) (x2 : real) (x3 : nat) (x4 : real) (x5 : real) (x6 : real) (x7 : nat) := ((real_add x0 x1) = (real_add x1 x0)) /\ (((real_add x0 (real_add x1 x2)) = (real_add (real_add x0 x1) x2)) /\ (((real_mul (real_pow x6 x3) (real_pow x6 x7)) = (real_pow x6 (Nat.add x3 x7))) /\ (((real_mul x6 (real_pow x6 x7)) = (real_pow x6 (S x7))) /\ (((real_mul (real_pow x6 x7) x6) = (real_pow x6 (S x7))) /\ (((real_mul x6 x6) = (real_pow x6 (NUMERAL (BIT0 (BIT1 0))))) /\ (((real_pow (real_mul x6 x4) x7) = (real_mul (real_pow x6 x7) (real_pow x4 x7))) /\ (((real_pow (real_pow x6 x3) x7) = (real_pow x6 (Nat.mul x3 x7))) /\ (((real_pow x6 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (((real_pow x6 (NUMERAL (BIT1 0))) = x6) /\ (((real_mul x6 (real_add x4 x5)) = (real_add (real_mul x6 x4) (real_mul x6 x5))) /\ ((real_pow x6 (S x7)) = (real_mul x6 (real_pow x6 x7))))))))))))).
