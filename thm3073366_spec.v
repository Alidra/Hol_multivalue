Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3073366 : forall (m : nat) (n : nat), ~ (~ (((int_of_num m) = (int_of_num n)) = ((int_abs (int_of_num m)) = (int_abs (int_of_num n))))).
