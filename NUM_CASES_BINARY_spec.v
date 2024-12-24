Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2976208 : forall P : nat -> Prop, (forall n : nat, P n) = ((forall n : nat, P (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n)) /\ (forall n : nat, P (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n) (NUMERAL (BIT1 0))))).
