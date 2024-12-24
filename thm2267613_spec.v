Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2267613 : forall (x : real), (exists n : nat, (real_abs x) = (real_of_num n)) = (exists n : nat, (x = (real_of_num n)) \/ (x = (real_neg (real_of_num n)))).
