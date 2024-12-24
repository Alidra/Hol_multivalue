Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : nat) := ((S x0) = (S x0)) \/ (Peano.le (S x0) x0).
Definition term7 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term11 := fun y0 : nat => Peano.le y0 y0.
Definition term15 := and (Peano.le (NUMERAL 0) (NUMERAL 0)).
Definition term22 (x0 : nat) := (Peano.le x0 x0) -> Peano.le (S x0) (S x0).
Definition term17 (x0 : nat) := imp ((fun y0 : nat => Peano.le y0 y0) x0).
Definition term28 := (Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (Peano.le y0 y0) -> Peano.le (S y0) (S y0)).
Definition term30 := imp ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (Peano.le y0 y0) -> Peano.le (S y0) (S y0))).
Definition term10 := (((fun y0 : nat => Peano.le y0 y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le y1 y1) y0) -> (fun y1 : nat => Peano.le y1 y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.le y1 y1) y0.
Definition term38 (x0 : nat) := True \/ (Peano.le (S x0) x0).
Definition term26 := forall y0 : nat, (Peano.le y0 y0) -> Peano.le (S y0) (S y0).
Definition term9 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term29 := imp (((fun y0 : nat => Peano.le y0 y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le y1 y1) y0) -> (fun y1 : nat => Peano.le y1 y1) (S y0))).
Definition term21 (x0 : nat) := ((fun y0 : nat => Peano.le y0 y0) x0) -> (fun y0 : nat => Peano.le y0 y0) (S x0).
Definition term25 := forall y0 : nat, ((fun y1 : nat => Peano.le y1 y1) y0) -> (fun y1 : nat => Peano.le y1 y1) (S y0).
Definition term27 := ((fun y0 : nat => Peano.le y0 y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le y1 y1) y0) -> (fun y1 : nat => Peano.le y1 y1) (S y0)).
Definition term36 (x0 : nat) := or ((S x0) = (S x0)).
Definition term23 := fun y0 : nat => ((fun y1 : nat => Peano.le y1 y1) y0) -> (fun y1 : nat => Peano.le y1 y1) (S y0).
Definition term16 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term31 := fun y0 : nat => (fun y1 : nat => Peano.le y1 y1) y0.
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term32 := forall y0 : nat, (fun y1 : nat => Peano.le y1 y1) y0.
Definition term19 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) (S x0).
Definition term34 := ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (Peano.le y0 y0) -> Peano.le (S y0) (S y0))) -> forall y0 : nat, Peano.le y0 y0.
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term12 := (fun y0 : nat => Peano.le y0 y0) (NUMERAL 0).
Definition term5 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term37 (x0 : nat) := Peano.le (S x0) x0.
Definition term14 := and ((fun y0 : nat => Peano.le y0 y0) (NUMERAL 0)).
Definition term6 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term33 := forall y0 : nat, Peano.le y0 y0.
Definition term18 (x0 : nat) := imp (Peano.le x0 x0).
Definition term8 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term4 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term20 (x0 : nat) := Peano.le (S x0) (S x0).
Definition term13 := Peano.le (NUMERAL 0) (NUMERAL 0).
Definition term24 := fun y0 : nat => (Peano.le y0 y0) -> Peano.le (S y0) (S y0).
