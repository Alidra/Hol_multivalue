Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302741 : forall (m : nat) (n : nat), (m = n) = (((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (m = n)).
