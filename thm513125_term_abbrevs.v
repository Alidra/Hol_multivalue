Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 := (forall y0 : nat, (Nat.add 0 y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term22 := (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0) /\ ((forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))))).
Definition term12 (x0 : nat) := @eq nat (Nat.add x0 0).
Definition term19 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term13 := fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0.
Definition term10 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term2 (x0 : nat) := @eq nat (Nat.add (NUMERAL 0) x0).
Definition term15 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term11 (x0 : nat) := @eq nat (Nat.add x0 (NUMERAL 0)).
Definition term1 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term14 := fun y0 : nat => (Nat.add y0 0) = y0.
Definition term18 := and (forall y0 : nat, (Nat.add y0 0) = y0).
Definition term17 := and (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0).
Definition term9 := and (forall y0 : nat, (Nat.add 0 y0) = y0).
Definition term8 := and (forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0).
Definition term7 := forall y0 : nat, (Nat.add 0 y0) = y0.
Definition term6 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term5 := fun y0 : nat => (Nat.add 0 y0) = y0.
Definition term21 := (forall y0 : nat, (Nat.add y0 0) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term20 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term0 := Nat.add (NUMERAL 0).
Definition term16 := forall y0 : nat, (Nat.add y0 0) = y0.
Definition term4 := fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0.
Definition term3 (x0 : nat) := @eq nat (Nat.add 0 x0).
