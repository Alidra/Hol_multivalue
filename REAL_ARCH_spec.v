Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1700438 : forall x : real, (real_lt (real_of_num (NUMERAL 0)) x) -> forall y : real, exists n : nat, real_lt y (real_mul (real_of_num n) x).
