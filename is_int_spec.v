Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2267614 : forall (x : real), (integer x) = (exists n : nat, (x = (real_of_num n)) \/ (x = (real_neg (real_of_num n)))).
