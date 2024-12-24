Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2404231 : forall (m : nat) (n : nat), ((int_lt (int_of_num m) (int_of_num n)) = (Peano.lt m n)) /\ (((int_lt (int_neg (int_of_num m)) (int_neg (int_of_num n))) = (Peano.lt n m)) /\ ((int_lt (int_neg (int_of_num m)) (int_of_num n)) = (~ ((m = (NUMERAL 0)) /\ (n = (NUMERAL 0)))))).
