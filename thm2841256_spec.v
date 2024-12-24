Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2841256 : forall m : nat, forall n : nat, (m = n) = ((int_of_num m) = (int_of_num n)).
