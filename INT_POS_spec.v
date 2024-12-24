Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307535 : forall n : nat, int_le (int_of_num (NUMERAL 0)) (int_of_num n).
