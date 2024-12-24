Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) := fun y0 : nat => Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT1 0))).
Definition term5 (x0 : nat) := forall y0 : nat, (NUMPAIR x0 y0) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT1 0)))).
Definition term6 := forall y0 : nat, forall y1 : nat, (NUMPAIR y0 y1) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) (NUMERAL (BIT1 0)))).
Definition term0 := fun y0 : nat => fun y1 : nat => Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) (NUMERAL (BIT1 0))).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (NUMPAIR x0 y0) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT1 0))))) x1.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (NUMPAIR y0 y1) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) (NUMERAL (BIT1 0))))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => fun y1 : nat => Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) (NUMERAL (BIT1 0)))) x0.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT1 0)))) x1.
Definition term4 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (NUMERAL (BIT1 0))).
