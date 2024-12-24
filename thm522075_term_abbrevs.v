Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : nat) := True /\ (Peano.le x0 0).
Definition term14 := fun y0 : nat => (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0)).
Definition term24 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) /\ (Peano.le x0 x1).
Definition term17 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.lt x0 x1).
Definition term8 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term30 := (forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0))).
Definition term26 (x0 : nat) := fun y0 : nat => ~ ((Peano.lt x0 y0) /\ (Peano.le y0 x0)).
Definition term19 (x0 : nat) := fun y0 : nat => ~ ((Peano.le x0 y0) /\ (Peano.lt y0 x0)).
Definition term4 := fun y0 : nat => (Peano.le y0 0) = ((Peano.le y0 0) /\ (Peano.le 0 y0)).
Definition term15 := forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0)).
Definition term6 := forall y0 : nat, (Peano.le y0 0) = ((Peano.le y0 0) /\ (Peano.le 0 y0)).
Definition term1 (x0 : nat) := (Peano.le x0 0) /\ (Peano.le 0 x0).
Definition term16 := and (forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0))).
Definition term10 := and (forall y0 : nat, (Peano.le y0 0) = ((Peano.le y0 0) /\ (Peano.le 0 y0))).
Definition term27 (x0 : nat) := forall y0 : nat, ~ ((Peano.lt x0 y0) /\ (Peano.le y0 x0)).
Definition term20 (x0 : nat) := forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.lt y0 x0)).
Definition term31 := (forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0))) /\ ((forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0)))).
Definition term29 := forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0)).
Definition term22 := forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0)).
Definition term3 (x0 : nat) := @eq Prop (Peano.le x0 0).
Definition term7 := forall y0 : nat, True.
Definition term25 (x0 : nat) (x1 : nat) := ~ ((Peano.lt x1 x0) /\ (Peano.le x0 x1)).
Definition term0 (x0 : nat) := and (Peano.le x0 0).
Definition term5 := fun y0 : nat => True.
Definition term2 (x0 : nat) := (Peano.le x0 0) /\ True.
Definition term18 (x0 : nat) (x1 : nat) := ~ ((Peano.le x1 x0) /\ (Peano.lt x0 x1)).
Definition term12 (x0 : nat) := (Peano.le 0 x0) /\ (Peano.le x0 0).
Definition term23 := and (forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))).
Definition term11 (x0 : nat) := and (Peano.le 0 x0).
Definition term32 := (forall y0 : nat, (Peano.le y0 0) = ((Peano.le y0 0) /\ (Peano.le 0 y0))) /\ ((forall y0 : nat, (Peano.le y0 0) = ((Peano.le 0 y0) /\ (Peano.le y0 0))) /\ ((forall y0 : nat, forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0))))).
Definition term28 := fun y0 : nat => forall y1 : nat, ~ ((Peano.lt y0 y1) /\ (Peano.le y1 y0)).
Definition term21 := fun y0 : nat => forall y1 : nat, ~ ((Peano.le y0 y1) /\ (Peano.lt y1 y0)).
Definition term9 (x0 : Prop) := forall y0 : nat, x0.
