Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt (NUMERAL 0) (Nat.pow x0 x1)).
Definition term24 (x0 : nat) (x1 : nat) := Peano.le (Nat.pow x0 x1) (NUMERAL 0).
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term18 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term30 (x0 : Prop) := ~ (~ x0).
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term40 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term28 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ (~ (~ (x1 = (NUMERAL 0)))).
Definition term33 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0)).
Definition term11 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term27 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term12 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term9 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term26 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term10 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term22 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL 0) (Nat.pow x0 x1).
Definition term38 (x0 : nat) := forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.pow y0 x0)) = ((~ (y0 = (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term29 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term16 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))).
Definition term43 := forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.pow y1 y0)) = ((~ (y1 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term36 (x0 : nat) := fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.pow y0 x0)) = ((~ (y0 = (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term23 (x0 : nat) (x1 : nat) := ~ (Peano.le (Nat.pow x0 x1) (NUMERAL 0)).
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term39 := forall y0 : nat, True.
Definition term25 (x0 : nat) (x1 : nat) := ~ ((x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0)))).
Definition term37 := fun y0 : nat => True.
Definition term35 (x0 : nat) (x1 : nat) := @eq Prop ((~ (x0 = (NUMERAL 0))) \/ (x1 = (NUMERAL 0))).
Definition term32 (x0 : nat) := or (~ (x0 = (NUMERAL 0))).
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term17 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term41 (x0 : Prop) := forall y0 : nat, x0.
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term31 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term19 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term42 := fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.pow y1 y0)) = ((~ (y1 = (NUMERAL 0))) \/ (y0 = (NUMERAL 0))).
Definition term14 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
