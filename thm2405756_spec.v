Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2405756 : forall (m : nat) (n : nat), (((int_mul (int_of_num m) (int_of_num n)) = (int_of_num (Nat.mul m n))) /\ ((int_mul (int_neg (int_of_num m)) (int_neg (int_of_num n))) = (int_of_num (Nat.mul m n)))) /\ (((int_mul (int_neg (int_of_num m)) (int_of_num n)) = (int_neg (int_of_num (Nat.mul m n)))) /\ ((int_mul (int_of_num m) (int_neg (int_of_num n))) = (int_neg (int_of_num (Nat.mul m n))))).
