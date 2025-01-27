Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term2 := real_of_num (NUMERAL 0).
Definition term0 := ~ (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term18 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term20 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_of_num x0)) (real_of_num x1).
Definition term9 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term12 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term19 := real_gt (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term6 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term5 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term14 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term8 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term7 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term22 := ((~ (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) -> False) -> real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term21 := (~ (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) -> False.
Definition term13 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term3 := real_of_num (NUMERAL (BIT1 0)).
Definition term16 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term23 := real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term17 := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term15 := real_add (real_of_num (NUMERAL 0)).
Definition term10 := NUMERAL (BIT1 0).
