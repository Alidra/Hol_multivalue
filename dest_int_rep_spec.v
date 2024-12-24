Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2267790 : forall i : int, exists n : nat, ((real_of_int i) = (real_of_num n)) \/ ((real_of_int i) = (real_neg (real_of_num n))).
