Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3174260 : (forall x : real, forall n : nat, (real_zpow x (int_of_num n)) = (real_pow x n)) /\ (forall x : real, forall n : nat, (real_zpow x (int_neg (int_of_num n))) = (real_inv (real_pow x n))).
