Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 := fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term2 (x0 : nat) := @eq nat (Nat.pow x0 0).
Definition term0 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term9 := and (forall y0 : nat, (Nat.pow y0 0) = (BIT1 0)).
Definition term8 := and (forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term10 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term12 := (forall y0 : nat, (Nat.pow y0 0) = (BIT1 0)) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))).
Definition term11 := (forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))).
Definition term5 := fun y0 : nat => (Nat.pow y0 0) = (BIT1 0).
Definition term6 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term7 := forall y0 : nat, (Nat.pow y0 0) = (BIT1 0).
Definition term1 (x0 : nat) := @eq nat (Nat.pow x0 (NUMERAL 0)).
Definition term3 := NUMERAL (BIT1 0).
