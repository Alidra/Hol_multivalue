Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem146250 : forall n : nat, Peano.le (NUMERAL (BIT1 0)) (Factorial.fact n).
