Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5404127 : forall (m : nat), (m = (NUMERAL 0)) -> forall x : nat, ((Peano.le m x) /\ (Peano.le x (NUMERAL 0))) = (x = (NUMERAL 0)).
