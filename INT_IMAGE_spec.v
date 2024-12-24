Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2295400 : forall x : int, (exists n : nat, x = (int_of_num n)) \/ (exists n : nat, x = (int_neg (int_of_num n))).
