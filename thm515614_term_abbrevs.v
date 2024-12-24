Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : nat) := @eq nat (Nat.mul 0 x0).
Definition term46 := (forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term45 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term6 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term49 := (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term23 (x0 : nat) := Nat.mul (BIT1 0) x0.
Definition term5 := fun y0 : nat => (Nat.mul 0 y0) = 0.
Definition term18 := and (forall y0 : nat, (Nat.mul y0 0) = 0).
Definition term9 := and (forall y0 : nat, (Nat.mul 0 y0) = 0).
Definition term12 (x0 : nat) := @eq nat (Nat.mul x0 0).
Definition term7 := forall y0 : nat, (Nat.mul 0 y0) = 0.
Definition term42 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term27 := fun y0 : nat => (Nat.mul (BIT1 0) y0) = y0.
Definition term26 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term37 := fun y0 : nat => (Nat.mul y0 (BIT1 0)) = y0.
Definition term34 (x0 : nat) := @eq nat (Nat.mul x0 (NUMERAL (BIT1 0))).
Definition term36 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term16 := forall y0 : nat, (Nat.mul y0 0) = 0.
Definition term39 := forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0.
Definition term38 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term11 (x0 : nat) := @eq nat (Nat.mul x0 (NUMERAL 0)).
Definition term24 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term17 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term8 := and (forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)).
Definition term41 := and (forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0).
Definition term40 := and (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0).
Definition term31 := and (forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0).
Definition term30 := and (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0).
Definition term25 (x0 : nat) := @eq nat (Nat.mul (BIT1 0) x0).
Definition term2 (x0 : nat) := @eq nat (Nat.mul (NUMERAL 0) x0).
Definition term29 := forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0.
Definition term28 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term33 (x0 : nat) := Nat.mul x0 (BIT1 0).
Definition term13 := fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term44 := (forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term43 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term14 := fun y0 : nat => (Nat.mul y0 0) = 0.
Definition term32 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term15 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term21 := Nat.mul (BIT1 0).
Definition term10 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term35 (x0 : nat) := @eq nat (Nat.mul x0 (BIT1 0)).
Definition term0 := Nat.mul (NUMERAL 0).
Definition term50 := (forall y0 : nat, (Nat.mul 0 y0) = 0) /\ ((forall y0 : nat, (Nat.mul y0 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))))).
Definition term1 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term20 := Nat.mul (NUMERAL (BIT1 0)).
Definition term47 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term48 := (forall y0 : nat, (Nat.mul y0 0) = 0) /\ ((forall y0 : nat, (Nat.mul (BIT1 0) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (BIT1 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term19 := NUMERAL (BIT1 0).
Definition term22 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term4 := fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
