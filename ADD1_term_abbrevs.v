Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term20 := S (NUMERAL 0).
Definition term1 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term16 (x0 : nat) := S (Nat.add (NUMERAL x0) (NUMERAL x0)).
Definition term27 := forall y0 : nat, (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term9 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term10 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term8 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term19 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term13 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term7 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term2 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term22 (x0 : nat) := Nat.add x0 (S (NUMERAL 0)).
Definition term28 := forall y0 : nat, True.
Definition term18 := S (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term11 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term12 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term21 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term14 (x0 : nat) := (fun y0 : nat => (NUMERAL (BIT1 y0)) = (S (Nat.add (NUMERAL y0) (NUMERAL y0)))) x0.
Definition term26 := fun y0 : nat => True.
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term0 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term24 (x0 : nat) := @eq nat (S x0).
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term23 (x0 : nat) := S (Nat.add x0 (NUMERAL 0)).
Definition term6 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term30 (x0 : Prop) := forall y0 : nat, x0.
Definition term25 := fun y0 : nat => (S y0) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term15 (x0 : nat) := NUMERAL (BIT1 x0).
Definition term17 := NUMERAL (BIT1 0).
Definition term4 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
