Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) := (fun y0 : nat => (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0.
Definition term1 := fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term0 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term3 := forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term4 := forall y0 : nat, (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term2 := fun y0 : nat => (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
