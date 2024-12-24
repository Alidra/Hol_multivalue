Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term37 := (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term26 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (S x0) x1).
Definition term35 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term5 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term9 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term23 := fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0.
Definition term6 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term15 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) x0).
Definition term24 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term22 (x0 : nat) := @eq nat (Nat.add x0 (NUMERAL 0)).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term14 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term4 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term25 := and (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0).
Definition term21 := and (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0).
Definition term34 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term18 := forall y0 : nat, True.
Definition term12 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term13 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term17 := fun y0 : nat => True.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term36 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term31 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 (S x1)).
Definition term32 (x0 : nat) := fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
Definition term30 := and (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))).
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term27 (x0 : nat) (x1 : nat) := @eq nat (S (Nat.add x0 x1)).
Definition term3 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term28 (x0 : nat) := fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term20 (x0 : Prop) := forall y0 : nat, x0.
Definition term33 := fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term29 := fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term16 := fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0.
Definition term11 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
