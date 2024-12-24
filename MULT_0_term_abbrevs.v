Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : nat) := ((fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0) -> (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) (S x0).
Definition term31 := @eq nat (NUMERAL 0).
Definition term27 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term6 := and ((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term43 (x0 : nat) := @eq nat (Nat.mul (S x0) (NUMERAL 0)).
Definition term14 (x0 : nat) := ((Nat.mul x0 (NUMERAL 0)) = (NUMERAL 0)) -> (Nat.mul (S x0) (NUMERAL 0)) = (NUMERAL 0).
Definition term3 := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) (NUMERAL 0).
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0)) x1.
Definition term28 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term24 := forall y0 : nat, (fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) y0.
Definition term19 := ((fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) (S y0)).
Definition term22 := imp (((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, ((Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) -> (Nat.mul (S y0) (NUMERAL 0)) = (NUMERAL 0))).
Definition term34 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term10 (x0 : nat) := imp ((Nat.mul x0 (NUMERAL 0)) = (NUMERAL 0)).
Definition term1 := (((fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) y0.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term21 := imp (((fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) (S y0))).
Definition term16 := fun y0 : nat => ((Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) -> (Nat.mul (S y0) (NUMERAL 0)) = (NUMERAL 0).
Definition term35 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term40 (x0 : nat) (x1 : nat) := Nat.mul (S x0) x1.
Definition term17 := forall y0 : nat, ((fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) (S y0).
Definition term20 := ((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, ((Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) -> (Nat.mul (S y0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term33 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term42 (x0 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)) (NUMERAL 0).
Definition term5 := and ((fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) (NUMERAL 0)).
Definition term7 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term15 := fun y0 : nat => ((fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) (S y0).
Definition term18 := forall y0 : nat, ((Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) -> (Nat.mul (S y0) (NUMERAL 0)) = (NUMERAL 0).
Definition term30 := @eq nat (Nat.mul (NUMERAL 0) (NUMERAL 0)).
Definition term36 := forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1).
Definition term38 (x0 : nat) := forall y0 : nat, (Nat.mul (S x0) y0) = (Nat.add (Nat.mul x0 y0) y0).
Definition term11 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) (S x0).
Definition term2 := fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term32 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) x0.
Definition term25 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term41 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1) x1.
Definition term8 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term23 := fun y0 : nat => (fun y1 : nat => (Nat.mul y1 (NUMERAL 0)) = (NUMERAL 0)) y0.
Definition term12 (x0 : nat) := Nat.mul (S x0) (NUMERAL 0).
Definition term4 := Nat.mul (NUMERAL 0) (NUMERAL 0).
Definition term29 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term9 (x0 : nat) := imp ((fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0).
Definition term26 := (((Nat.mul (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, ((Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) -> (Nat.mul (S y0) (NUMERAL 0)) = (NUMERAL 0))) -> forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
