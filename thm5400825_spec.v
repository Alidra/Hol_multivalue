Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5400825 : forall (m : nat) (h1 : ~ (m = (NUMERAL 0))), ~ (m = (NUMERAL 0)).
