Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := ((real_mul (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.mul x0 x1))) /\ ((real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num (Nat.mul x0 x1))).