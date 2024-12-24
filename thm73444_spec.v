Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem73444 : forall P : nat -> Prop, ((P 0) /\ (forall n : nat, (P n) -> P (S n))) -> forall n : nat, P n.
