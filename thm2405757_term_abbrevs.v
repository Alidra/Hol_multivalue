Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := ((int_mul (int_neg (int_of_num x0)) (int_of_num x1)) = (int_neg (int_of_num (Nat.mul x0 x1)))) /\ ((int_mul (int_of_num x0) (int_neg (int_of_num x1))) = (int_neg (int_of_num (Nat.mul x0 x1)))).
