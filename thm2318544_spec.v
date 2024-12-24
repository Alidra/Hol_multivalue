Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2318544 : forall (n : nat), (fun n' : nat => (real_of_int (int_of_num n')) = (real_of_num n')) n.
