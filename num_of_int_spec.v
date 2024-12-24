Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2833930 : forall x : int, (num_of_int x) = (@ε nat (fun n : nat => (int_of_num n) = x)).
