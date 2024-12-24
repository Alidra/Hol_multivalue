Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1981223 : forall (n : nat) (m : nat), ((real_inv (real_of_num n)) = (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num n))) /\ (((real_inv (real_neg (real_of_num n))) = (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num n))) /\ (((real_inv (real_div (real_of_num m) (real_of_num n))) = (real_div (real_of_num n) (real_of_num m))) /\ (((real_inv (real_div (real_neg (real_of_num m)) (real_of_num n))) = (real_div (real_neg (real_of_num n)) (real_of_num m))) /\ (((real_inv (DECIMAL m n)) = (real_div (real_of_num n) (real_of_num m))) /\ ((real_inv (real_neg (DECIMAL m n))) = (real_div (real_neg (real_of_num n)) (real_of_num m))))))).
