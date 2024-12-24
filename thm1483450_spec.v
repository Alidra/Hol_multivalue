Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483450 : forall (a : real), (real_add a (real_of_num (NUMERAL 0))) = a.
