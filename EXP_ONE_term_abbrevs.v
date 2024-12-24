Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (x0 : nat) := ((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) x0) -> (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (S x0).
Definition term8 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) x0.
Definition term9 (x0 : nat) := Nat.pow (NUMERAL (BIT1 0)) x0.
Definition term34 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term44 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) (Nat.pow (NUMERAL (BIT1 0)) x0).
Definition term24 := fun y0 : nat => (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0.
Definition term40 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term3 := (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0).
Definition term25 := forall y0 : nat, (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0.
Definition term20 := ((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0)).
Definition term42 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term1 := (((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0.
Definition term41 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term15 (x0 : nat) := ((Nat.pow (NUMERAL (BIT1 0)) x0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S x0)) = (NUMERAL (BIT1 0)).
Definition term13 (x0 : nat) := Nat.pow (NUMERAL (BIT1 0)) (S x0).
Definition term12 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (S x0).
Definition term30 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term22 := imp (((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0))).
Definition term45 (x0 : nat) := @eq nat (Nat.pow (NUMERAL (BIT1 0)) (S x0)).
Definition term18 := forall y0 : nat, ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0).
Definition term7 := and ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term6 := and ((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) (NUMERAL 0)).
Definition term11 (x0 : nat) := imp ((Nat.pow (NUMERAL (BIT1 0)) x0) = (NUMERAL (BIT1 0))).
Definition term29 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term16 := fun y0 : nat => ((fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) y0) -> (fun y1 : nat => (Nat.pow (NUMERAL (BIT1 0)) y1) = (NUMERAL (BIT1 0))) (S y0).
Definition term38 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term4 := Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term2 := fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0)).
Definition term31 := @eq nat (Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term35 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term43 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term26 := forall y0 : nat, (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0)).
Definition term36 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) x0.
Definition term21 := ((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0))).
Definition term32 := @eq nat (NUMERAL (BIT1 0)).
Definition term39 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term28 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term17 := fun y0 : nat => ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0)).
Definition term10 (x0 : nat) := imp ((fun y0 : nat => (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) x0).
Definition term19 := forall y0 : nat, ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0)).
Definition term33 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term27 := (((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0)))) -> forall y0 : nat, (Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0)).
Definition term5 := NUMERAL (BIT1 0).
Definition term37 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term23 := imp (((Nat.pow (NUMERAL (BIT1 0)) (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, ((Nat.pow (NUMERAL (BIT1 0)) y0) = (NUMERAL (BIT1 0))) -> (Nat.pow (NUMERAL (BIT1 0)) (S y0)) = (NUMERAL (BIT1 0)))).
