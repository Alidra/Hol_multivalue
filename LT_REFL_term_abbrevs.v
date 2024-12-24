Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : nat) := Peano.lt (S x0) (S x0).
Definition term27 := forall y0 : nat, (fun y1 : nat => ~ (Peano.lt y1 y1)) y0.
Definition term29 := ((~ (Peano.lt (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (~ (Peano.lt y0 y0)) -> ~ (Peano.lt (S y0) (S y0)))) -> forall y0 : nat, ~ (Peano.lt y0 y0).
Definition term17 (x0 : nat) := (~ (Peano.lt x0 x0)) -> ~ (Peano.lt (S x0) (S x0)).
Definition term22 := ((fun y0 : nat => ~ (Peano.lt y0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ (Peano.lt y1 y1)) y0) -> (fun y1 : nat => ~ (Peano.lt y1 y1)) (S y0)).
Definition term9 := and (~ (Peano.lt (NUMERAL 0) (NUMERAL 0))).
Definition term31 (x0 : nat) := forall y0 : nat, (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0).
Definition term7 := ~ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term16 (x0 : nat) := ((fun y0 : nat => ~ (Peano.lt y0 y0)) x0) -> (fun y0 : nat => ~ (Peano.lt y0 y0)) (S x0).
Definition term4 := (((fun y0 : nat => ~ (Peano.lt y0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ (Peano.lt y1 y1)) y0) -> (fun y1 : nat => ~ (Peano.lt y1 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => ~ (Peano.lt y1 y1)) y0.
Definition term0 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term3 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term24 := imp (((fun y0 : nat => ~ (Peano.lt y0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => ~ (Peano.lt y1 y1)) y0) -> (fun y1 : nat => ~ (Peano.lt y1 y1)) (S y0))).
Definition term21 := forall y0 : nat, (~ (Peano.lt y0 y0)) -> ~ (Peano.lt (S y0) (S y0)).
Definition term23 := (~ (Peano.lt (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (~ (Peano.lt y0 y0)) -> ~ (Peano.lt (S y0) (S y0))).
Definition term20 := forall y0 : nat, ((fun y1 : nat => ~ (Peano.lt y1 y1)) y0) -> (fun y1 : nat => ~ (Peano.lt y1 y1)) (S y0).
Definition term8 := and ((fun y0 : nat => ~ (Peano.lt y0 y0)) (NUMERAL 0)).
Definition term12 (x0 : nat) := imp ((fun y0 : nat => ~ (Peano.lt y0 y0)) x0).
Definition term1 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term36 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term34 (x0 : nat) := (~ (Peano.lt x0 x0)) -> (Peano.lt x0 x0) = False.
Definition term14 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) (S x0).
Definition term15 (x0 : nat) := ~ (Peano.lt (S x0) (S x0)).
Definition term13 (x0 : nat) := imp (~ (Peano.lt x0 x0)).
Definition term11 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term19 := fun y0 : nat => (~ (Peano.lt y0 y0)) -> ~ (Peano.lt (S y0) (S y0)).
Definition term28 := forall y0 : nat, ~ (Peano.lt y0 y0).
Definition term32 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (S x0) (S y0)) = (Peano.lt x0 y0)) x1.
Definition term5 := fun y0 : nat => ~ (Peano.lt y0 y0).
Definition term2 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term30 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (S y0) (S y1)) = (Peano.lt y0 y1)) x0.
Definition term25 := imp ((~ (Peano.lt (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, (~ (Peano.lt y0 y0)) -> ~ (Peano.lt (S y0) (S y0)))).
Definition term10 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term33 (x0 : nat) (x1 : nat) := Peano.lt (S x0) (S x1).
Definition term26 := fun y0 : nat => (fun y1 : nat => ~ (Peano.lt y1 y1)) y0.
Definition term18 := fun y0 : nat => ((fun y1 : nat => ~ (Peano.lt y1 y1)) y0) -> (fun y1 : nat => ~ (Peano.lt y1 y1)) (S y0).
Definition term6 := (fun y0 : nat => ~ (Peano.lt y0 y0)) (NUMERAL 0).
