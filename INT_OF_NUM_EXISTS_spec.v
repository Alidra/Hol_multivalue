Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2330500 : forall x : int, (exists n : nat, x = (int_of_num n)) = (int_le (int_of_num (NUMERAL 0)) x).
