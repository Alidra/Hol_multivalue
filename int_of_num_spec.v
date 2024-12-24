Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2271820 : forall n : nat, (int_of_num n) = (int_of_real (real_of_num n)).
