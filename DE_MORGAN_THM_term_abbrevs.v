Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (x0 : Prop) := fun y0 : Prop => (~ (y0 \/ x0)) = ((~ y0) /\ (~ x0)).
Definition term18 (x0 : Prop) := @eq Prop (~ (False /\ x0)).
Definition term16 := or (~ True).
Definition term13 (x0 : Prop) := (~ False) \/ (~ x0).
Definition term6 (x0 : Prop) := (~ True) \/ (~ x0).
Definition term35 (x0 : Prop) := False /\ (~ x0).
Definition term32 (x0 : Prop) := (~ False) /\ (~ x0).
Definition term30 (x0 : Prop) := (fun y0 : Prop => (~ (y0 \/ x0)) = ((~ y0) /\ (~ x0))) False.
Definition term9 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term39 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term14 (x0 : Prop) := @eq Prop (~ (True /\ x0)).
Definition term28 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term8 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term40 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term19 := or (~ False).
Definition term25 (x0 : Prop) := (~ True) /\ (~ x0).
Definition term2 (x0 : Prop) := fun y0 : Prop => (~ (y0 /\ x0)) = ((~ y0) \/ (~ x0)).
Definition term24 (x0 : Prop) := ~ (True \/ x0).
Definition term11 (x0 : Prop) := (fun y0 : Prop => (~ (y0 /\ x0)) = ((~ y0) \/ (~ x0))) False.
Definition term17 (x0 : Prop) := False \/ (~ x0).
Definition term10 (x0 : Prop) (x1 : Prop) := @eq Prop ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))).
Definition term20 (x0 : Prop) := True \/ (~ x0).
Definition term15 (x0 : Prop) := @eq Prop (~ x0).
Definition term27 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term29 (x0 : Prop) (x1 : Prop) := @eq Prop ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term34 := and (~ True).
Definition term38 (x0 : Prop) := True /\ (~ x0).
Definition term12 (x0 : Prop) := ~ (False /\ x0).
Definition term26 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (~ (y0 \/ x0)) = ((~ y0) /\ (~ x0))) x1).
Definition term7 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (~ (y0 /\ x0)) = ((~ y0) \/ (~ x0))) x1).
Definition term33 (x0 : Prop) := @eq Prop (~ (True \/ x0)).
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term41 := forall y0 : Prop, forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1))).
Definition term31 (x0 : Prop) := ~ (False \/ x0).
Definition term3 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (y0 /\ x0)) = ((~ y0) \/ (~ x0))) x1.
Definition term4 (x0 : Prop) := (fun y0 : Prop => (~ (y0 /\ x0)) = ((~ y0) \/ (~ x0))) True.
Definition term23 (x0 : Prop) := (fun y0 : Prop => (~ (y0 \/ x0)) = ((~ y0) /\ (~ x0))) True.
Definition term36 (x0 : Prop) := @eq Prop (~ (False \/ x0)).
Definition term37 := and (~ False).
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term5 (x0 : Prop) := ~ (True /\ x0).
Definition term22 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (y0 \/ x0)) = ((~ y0) /\ (~ x0))) x1.
