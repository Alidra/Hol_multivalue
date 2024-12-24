Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) := ((fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) x0) -> (fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) (S x0).
Definition term3 := (fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) (NUMERAL 0).
Definition term30 := @eq nat (NUMERAL 0).
Definition term24 := forall y0 : nat, (Nat.sub y0 y0) = (NUMERAL 0).
Definition term6 := and ((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term2 := fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0).
Definition term9 (x0 : nat) := imp ((Nat.sub x0 x0) = (NUMERAL 0)).
Definition term7 (x0 : nat) := (fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) x0.
Definition term32 (x0 : nat) := forall y0 : nat, (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0)) x1.
Definition term23 := forall y0 : nat, (fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) y0.
Definition term18 := ((fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) (S y0)).
Definition term21 := imp (((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, ((Nat.sub y0 y0) = (NUMERAL 0)) -> (Nat.sub (S y0) (S y0)) = (NUMERAL 0))).
Definition term1 := (((fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) y0.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term20 := imp (((fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) (S y0))).
Definition term35 (x0 : nat) := @eq nat (Nat.sub (S x0) (S x0)).
Definition term26 (x0 : nat) := (fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((Nat.sub y0 (NUMERAL 0)) = y0)) x0.
Definition term16 := forall y0 : nat, ((fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) (S y0).
Definition term19 := ((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, ((Nat.sub y0 y0) = (NUMERAL 0)) -> (Nat.sub (S y0) (S y0)) = (NUMERAL 0)).
Definition term11 (x0 : nat) := Nat.sub (S x0) (S x0).
Definition term15 := fun y0 : nat => ((Nat.sub y0 y0) = (NUMERAL 0)) -> (Nat.sub (S y0) (S y0)) = (NUMERAL 0).
Definition term28 (x0 : nat) := Nat.sub (NUMERAL 0) x0.
Definition term5 := and ((fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) (NUMERAL 0)).
Definition term10 (x0 : nat) := (fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) (S x0).
Definition term14 := fun y0 : nat => ((fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) (S y0).
Definition term17 := forall y0 : nat, ((Nat.sub y0 y0) = (NUMERAL 0)) -> (Nat.sub (S y0) (S y0)) = (NUMERAL 0).
Definition term34 (x0 : nat) (x1 : nat) := Nat.sub (S x0) (S x1).
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) x0.
Definition term27 (x0 : nat) := ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)) /\ ((Nat.sub x0 (NUMERAL 0)) = x0).
Definition term29 := @eq nat (Nat.sub (NUMERAL 0) (NUMERAL 0)).
Definition term22 := fun y0 : nat => (fun y1 : nat => (Nat.sub y1 y1) = (NUMERAL 0)) y0.
Definition term4 := Nat.sub (NUMERAL 0) (NUMERAL 0).
Definition term8 (x0 : nat) := imp ((fun y0 : nat => (Nat.sub y0 y0) = (NUMERAL 0)) x0).
Definition term25 := (((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, ((Nat.sub y0 y0) = (NUMERAL 0)) -> (Nat.sub (S y0) (S y0)) = (NUMERAL 0))) -> forall y0 : nat, (Nat.sub y0 y0) = (NUMERAL 0).
Definition term13 (x0 : nat) := ((Nat.sub x0 x0) = (NUMERAL 0)) -> (Nat.sub (S x0) (S x0)) = (NUMERAL 0).
