Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : nat) := NUMERAL (BIT0 x0).
Definition term8 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term21 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0) (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term18 := Nat.mul (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term20 (x0 : nat) := Nat.mul (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) x0.
Definition term23 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term16 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term17 := Nat.mul (NUMERAL (BIT0 (BIT1 0))).
Definition term19 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term24 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term25 (x0 : nat) := @eq nat (Nat.add x0 x0).
Definition term26 := forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term9 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term10 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term12 (x0 : nat) := (fun y0 : nat => (NUMERAL (BIT0 y0)) = (Nat.add (NUMERAL y0) (NUMERAL y0))) x0.
Definition term15 := NUMERAL (BIT0 (BIT1 0)).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term14 (x0 : nat) := Nat.add (NUMERAL x0) (NUMERAL x0).
Definition term7 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term22 := NUMERAL (BIT1 0).
Definition term11 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
