Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2968656 : forall P : nat -> Prop, ((P (NUMERAL 0)) /\ (forall n : nat, (P n) -> (P (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n)) /\ (P (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n) (NUMERAL (BIT1 0)))))) -> forall n : nat, P n.
