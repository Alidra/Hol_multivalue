Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5418285 : forall (m : nat) (h1 : ~ (m = (NUMERAL 0))), forall x : nat, ~ ((Peano.le m x) /\ (Peano.le x (NUMERAL 0))).
