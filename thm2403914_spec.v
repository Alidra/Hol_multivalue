Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2403914 : forall (m : nat) (n : nat), ((int_le (int_of_num m) (int_of_num n)) = (Peano.le m n)) /\ (((int_le (int_neg (int_of_num m)) (int_neg (int_of_num n))) = (Peano.le n m)) /\ ((int_le (int_of_num m) (int_neg (int_of_num n))) = ((m = (NUMERAL 0)) /\ (n = (NUMERAL 0))))).
