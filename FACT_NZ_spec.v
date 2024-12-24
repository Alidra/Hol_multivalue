Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem146288 : forall n : nat, ~ ((Factorial.fact n) = (NUMERAL 0)).
