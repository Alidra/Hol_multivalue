Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1365723 : forall (m : nat) (n : nat), ((real_lt (real_neg (real_of_num m)) (real_neg (real_of_num n))) = (Peano.lt n m)) /\ ((real_lt (real_neg (real_of_num m)) (real_of_num n)) = (~ ((m = (NUMERAL 0)) /\ (n = (NUMERAL 0))))).
