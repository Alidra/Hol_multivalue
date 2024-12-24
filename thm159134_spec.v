Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem159134 : forall (n : nat), (n = (NUMERAL 0)) \/ (~ (n = (NUMERAL 0))).
