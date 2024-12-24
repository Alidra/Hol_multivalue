Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483462 : forall (a : real), (real_mul a (real_of_num (NUMERAL (BIT1 0)))) = a.
