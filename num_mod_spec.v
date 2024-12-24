Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2837524 : forall n : nat, forall x : nat, forall y : nat, (num_mod n x y) = (int_mod (int_of_num n) (int_of_num x) (int_of_num y)).
