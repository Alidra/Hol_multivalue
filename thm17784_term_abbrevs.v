Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : Prop) := @eq Prop (False = x0).
Definition term14 := or (~ True).
Definition term23 (x0 : Prop) := (~ x0) /\ True.
Definition term11 (x0 : Prop) := @eq Prop (True = x0).
Definition term7 (x0 : Prop) (x1 : Prop) := (x0 \/ (~ x1)) /\ ((~ x0) \/ x1).
Definition term10 (x0 : Prop) := (False \/ (~ x0)) /\ ((~ False) \/ x0).
Definition term3 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = x0) = ((y0 \/ (~ x0)) /\ ((~ y0) \/ x0))) x1.
Definition term13 (x0 : Prop) := and (True \/ (~ x0)).
Definition term22 (x0 : Prop) := (~ False) \/ x0.
Definition term21 := or (~ False).
Definition term18 (x0 : Prop) := False \/ (~ x0).
Definition term12 (x0 : Prop) := True \/ (~ x0).
Definition term15 (x0 : Prop) := (~ True) \/ x0.
Definition term9 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((y0 \/ (~ x0)) /\ ((~ y0) \/ x0))) False.
Definition term5 (x0 : Prop) := (True \/ (~ x0)) /\ ((~ True) \/ x0).
Definition term17 (x0 : Prop) := @eq Prop (~ x0).
Definition term6 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = x0) = ((y0 \/ (~ x0)) /\ ((~ y0) \/ x0))) x1).
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term20 (x0 : Prop) := and (~ x0).
Definition term2 (x0 : Prop) := fun y0 : Prop => (y0 = x0) = ((y0 \/ (~ x0)) /\ ((~ y0) \/ x0)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term8 (x0 : Prop) (x1 : Prop) := @eq Prop ((x0 = x1) = ((x0 \/ (~ x1)) /\ ((~ x0) \/ x1))).
Definition term19 (x0 : Prop) := and (False \/ (~ x0)).
Definition term4 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((y0 \/ (~ x0)) /\ ((~ y0) \/ x0))) True.
