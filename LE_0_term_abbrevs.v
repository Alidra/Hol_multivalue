Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term2 := fun y0 : nat => Peano.le (NUMERAL 0) y0.
Definition term38 (x0 : nat) := ((NUMERAL 0) = (S x0)) \/ True.
Definition term6 := and (Peano.le (NUMERAL 0) (NUMERAL 0)).
Definition term9 (x0 : nat) := imp ((fun y0 : nat => Peano.le (NUMERAL 0) y0) x0).
Definition term20 := (Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (Peano.le (NUMERAL 0) y0) -> Peano.le (NUMERAL 0) (S y0)).
Definition term22 := imp ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (Peano.le (NUMERAL 0) y0) -> Peano.le (NUMERAL 0) (S y0))).
Definition term7 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term1 := (((fun y0 : nat => Peano.le (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (NUMERAL 0) y1) y0) -> (fun y1 : nat => Peano.le (NUMERAL 0) y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.le (NUMERAL 0) y1) y0.
Definition term18 := forall y0 : nat, (Peano.le (NUMERAL 0) y0) -> Peano.le (NUMERAL 0) (S y0).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term21 := imp (((fun y0 : nat => Peano.le (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (NUMERAL 0) y1) y0) -> (fun y1 : nat => Peano.le (NUMERAL 0) y1) (S y0))).
Definition term13 (x0 : nat) := ((fun y0 : nat => Peano.le (NUMERAL 0) y0) x0) -> (fun y0 : nat => Peano.le (NUMERAL 0) y0) (S x0).
Definition term16 := fun y0 : nat => (Peano.le (NUMERAL 0) y0) -> Peano.le (NUMERAL 0) (S y0).
Definition term36 (x0 : nat) := ((NUMERAL 0) = (S x0)) \/ (Peano.le (NUMERAL 0) x0).
Definition term17 := forall y0 : nat, ((fun y1 : nat => Peano.le (NUMERAL 0) y1) y0) -> (fun y1 : nat => Peano.le (NUMERAL 0) y1) (S y0).
Definition term19 := ((fun y0 : nat => Peano.le (NUMERAL 0) y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.le (NUMERAL 0) y1) y0) -> (fun y1 : nat => Peano.le (NUMERAL 0) y1) (S y0)).
Definition term23 := fun y0 : nat => (fun y1 : nat => Peano.le (NUMERAL 0) y1) y0.
Definition term15 := fun y0 : nat => ((fun y1 : nat => Peano.le (NUMERAL 0) y1) y0) -> (fun y1 : nat => Peano.le (NUMERAL 0) y1) (S y0).
Definition term11 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) (S x0).
Definition term30 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term25 := forall y0 : nat, Peano.le (NUMERAL 0) y0.
Definition term24 := forall y0 : nat, (fun y1 : nat => Peano.le (NUMERAL 0) y1) y0.
Definition term8 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term32 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term37 (x0 : nat) := or ((NUMERAL 0) = (S x0)).
Definition term35 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term14 (x0 : nat) := (Peano.le (NUMERAL 0) x0) -> Peano.le (NUMERAL 0) (S x0).
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term12 (x0 : nat) := Peano.le (NUMERAL 0) (S x0).
Definition term5 := and ((fun y0 : nat => Peano.le (NUMERAL 0) y0) (NUMERAL 0)).
Definition term27 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term10 (x0 : nat) := imp (Peano.le (NUMERAL 0) x0).
Definition term29 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term34 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term26 := ((Peano.le (NUMERAL 0) (NUMERAL 0)) /\ (forall y0 : nat, (Peano.le (NUMERAL 0) y0) -> Peano.le (NUMERAL 0) (S y0))) -> forall y0 : nat, Peano.le (NUMERAL 0) y0.
Definition term3 := (fun y0 : nat => Peano.le (NUMERAL 0) y0) (NUMERAL 0).
Definition term4 := Peano.le (NUMERAL 0) (NUMERAL 0).
