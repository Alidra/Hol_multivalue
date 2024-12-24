Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3117502 : forall (x : nat) (y : nat) (n : nat), ((fun n' : nat => (@eq2 nat x y (num_mod n')) = (@eq2 int (int_of_num x) (int_of_num y) (int_mod (int_of_num n')))) n) = ((@eq2 nat x y (num_mod n)) = (@eq2 int (int_of_num x) (int_of_num y) (int_mod (int_of_num n)))).
