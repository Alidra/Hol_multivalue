Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1699575 : forall x : real, exists n : nat, real_lt x (real_of_num n).
