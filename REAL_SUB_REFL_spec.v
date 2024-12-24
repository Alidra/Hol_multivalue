Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1505261 : forall x : real, (real_sub x x) = (real_of_num (NUMERAL 0)).
