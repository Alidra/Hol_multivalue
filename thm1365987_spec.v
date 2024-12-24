Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1365987 : forall (m : nat) (n : nat), ((real_ge (real_of_num m) (real_neg (real_of_num n))) = True) /\ (((real_ge (real_of_num m) (real_of_num n)) = (Peano.le n m)) /\ (((real_ge (real_neg (real_of_num m)) (real_neg (real_of_num n))) = (Peano.le m n)) /\ ((real_ge (real_neg (real_of_num m)) (real_of_num n)) = ((m = (NUMERAL 0)) /\ (n = (NUMERAL 0)))))).
