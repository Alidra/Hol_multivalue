Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300474 : forall n : nat, (int_abs (int_of_num n)) = (int_of_num n).
