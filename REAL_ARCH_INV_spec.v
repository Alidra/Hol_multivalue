Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1703820 : forall e : real, (real_lt (real_of_num (NUMERAL 0)) e) = (exists n : nat, (~ (n = (NUMERAL 0))) /\ ((real_lt (real_of_num (NUMERAL 0)) (real_inv (real_of_num n))) /\ (real_lt (real_inv (real_of_num n)) e))).
