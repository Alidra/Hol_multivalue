Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3169233 : forall x : real, forall n : nat, (real_pow x n) = (real_zpow x (int_of_num n)).
