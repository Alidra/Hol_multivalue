Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2259353 : forall x : real, (integer x) = (exists n : nat, (real_abs x) = (real_of_num n)).
