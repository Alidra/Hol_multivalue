Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem75586 : forall P : nat -> Prop, ((P (NUMERAL 0)) /\ (forall n : nat, (P n) -> P (S n))) -> forall n : nat, P n.
