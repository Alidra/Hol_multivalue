Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem75623 : forall (P : nat -> Prop), ((fun P' : nat -> Prop => ((P' (NUMERAL 0)) /\ (forall n : nat, (P' n) -> P' (S n))) -> forall n : nat, P' n) P) = (((P (NUMERAL 0)) /\ (forall n : nat, (P n) -> P (S n))) -> forall n : nat, P n).
