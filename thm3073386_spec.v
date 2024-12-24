Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3073386 : forall (m : nat) (n : nat), ((fun n' : nat => (m = n') = ((int_of_num m) = (int_of_num n'))) n) = ((m = n) = ((int_of_num m) = (int_of_num n))).
