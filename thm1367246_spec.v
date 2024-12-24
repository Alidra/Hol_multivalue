Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1367246 : forall (m : nat) (n : nat), (((real_mul (real_of_num m) (real_of_num n)) = (real_of_num (Nat.mul m n))) /\ ((real_mul (real_neg (real_of_num m)) (real_neg (real_of_num n))) = (real_of_num (Nat.mul m n)))) /\ (((real_mul (real_neg (real_of_num m)) (real_of_num n)) = (real_neg (real_of_num (Nat.mul m n)))) /\ ((real_mul (real_of_num m) (real_neg (real_of_num n))) = (real_neg (real_of_num (Nat.mul m n))))).
