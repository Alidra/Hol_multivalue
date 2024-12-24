Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem159136 : forall (n : nat) (h1 : ~ (n = (NUMERAL 0))), ~ (n = (NUMERAL 0)).
