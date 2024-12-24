Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL (BIT1 0)))) /\ (forall y1 : nat, (num_divides y1 y0) -> (y1 = (NUMERAL (BIT1 0))) \/ (y1 = y0))) x0.
Definition term0 := fun y0 : nat => (~ (y0 = (NUMERAL (BIT1 0)))) /\ (forall y1 : nat, (num_divides y1 y0) -> (y1 = (NUMERAL (BIT1 0))) \/ (y1 = y0)).
Definition term3 := forall y0 : nat, (prime y0) = ((~ (y0 = (NUMERAL (BIT1 0)))) /\ (forall y1 : nat, (num_divides y1 y0) -> (y1 = (NUMERAL (BIT1 0))) \/ (y1 = y0))).
Definition term2 (x0 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)).
Definition term4 (x0 : nat) := (fun y0 : nat => (prime y0) = ((~ (y0 = (NUMERAL (BIT1 0)))) /\ (forall y1 : nat, (num_divides y1 y0) -> (y1 = (NUMERAL (BIT1 0))) \/ (y1 = y0)))) x0.
