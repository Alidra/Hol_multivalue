Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem76132 : forall m : nat, (m = (NUMERAL 0)) \/ (exists n : nat, m = (S n)).
