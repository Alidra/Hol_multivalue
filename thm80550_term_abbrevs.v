Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 := (forall y0 : nat, (Nat.add 0 y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term23 := (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term13 (x0 : nat) := @eq nat (Nat.add x0 0).
Definition term20 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term45 := @eq nat (NUMERAL (BIT0 (BIT1 0))).
Definition term27 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term39 := Nat.add (BIT1 0).
Definition term14 := fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0.
Definition term11 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term33 (x0 : nat) := S (Nat.add x0 x0).
Definition term3 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) x0).
Definition term16 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term34 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term12 (x0 : nat) := @eq nat (Nat.add x0 (NUMERAL 0)).
Definition term28 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term0 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term2 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term15 := fun y0 : nat => (Nat.add y0 0) = y0.
Definition term46 := @eq nat (S (S 0)).
Definition term30 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term19 := and (forall y0 : nat, (Nat.add y0 0) = y0).
Definition term18 := and (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0).
Definition term10 := and (forall y0 : nat, (Nat.add 0 y0) = y0).
Definition term9 := and (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0).
Definition term40 := Nat.add (S 0).
Definition term25 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term48 := S (NUMERAL (BIT1 0)).
Definition term8 := forall y0 : nat, (Nat.add 0 y0) = y0.
Definition term7 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term31 (x0 : nat) := (fun y0 : nat => (Nat.add 0 y0) = y0) x0.
Definition term38 := S (Nat.add 0 0).
Definition term6 := fun y0 : nat => (Nat.add 0 y0) = y0.
Definition term32 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term22 := (forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term21 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term35 := NUMERAL (BIT0 (BIT1 0)).
Definition term1 := Nat.add (NUMERAL 0).
Definition term37 := Nat.add (BIT1 0) (BIT1 0).
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term42 := S (Nat.add 0 (S 0)).
Definition term43 := Nat.add 0 (S 0).
Definition term17 := forall y0 : nat, (Nat.add y0 0) = y0.
Definition term36 := BIT0 (BIT1 0).
Definition term44 := S (S 0).
Definition term41 := Nat.add (S 0) (S 0).
Definition term5 := fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0.
Definition term4 (x0 : nat) := @eq nat (Nat.add 0 x0).
Definition term29 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term47 := NUMERAL (BIT1 0).
