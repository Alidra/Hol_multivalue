Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1366271 : forall (m : nat) (n : nat), ((real_gt (real_of_num m) (real_of_num n)) = (Peano.lt n m)) /\ (((real_gt (real_neg (real_of_num m)) (real_neg (real_of_num n))) = (Peano.lt m n)) /\ ((real_gt (real_of_num m) (real_neg (real_of_num n))) = (~ ((m = (NUMERAL 0)) /\ (n = (NUMERAL 0)))))).
