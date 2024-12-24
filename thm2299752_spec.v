Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299752 : forall n : nat, (real_of_num n) = (real_of_int (int_of_num n)).
