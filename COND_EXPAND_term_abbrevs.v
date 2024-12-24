Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 := or (~ True).
Definition term5 (x0 : Prop) (x1 : Prop) := ((~ True) \/ x0) /\ (True \/ x1).
Definition term15 (x0 : Prop) (x1 : Prop) := @eq Prop (@COND Prop False x0 x1).
Definition term11 (x0 : Prop) (x1 : Prop) := @eq Prop (@COND Prop True x0 x1).
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (@COND Prop y0 x0 x1) = (((~ y0) \/ x0) /\ (y0 \/ x1))) x2.
Definition term17 (x0 : Prop) := (~ False) \/ x0.
Definition term16 := or (~ False).
Definition term2 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (@COND Prop y0 x0 x1) = (((~ y0) \/ x0) /\ (y0 \/ x1)).
Definition term13 (x0 : Prop) := (~ True) \/ x0.
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term21 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, (@COND Prop y0 y1 y2) = (((~ y0) \/ y1) /\ (y0 \/ y2)).
Definition term20 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (@COND Prop x0 y0 y1) = (((~ x0) \/ y0) /\ (x0 \/ y1)).
Definition term9 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (@COND Prop y0 x0 x1) = (((~ y0) \/ x0) /\ (y0 \/ x1))) False.
Definition term10 (x0 : Prop) (x1 : Prop) := ((~ False) \/ x0) /\ (False \/ x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((@COND Prop x1 x0 x2) = (((~ x1) \/ x0) /\ (x1 \/ x2))).
Definition term19 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (@COND Prop x1 x0 y0) = (((~ x1) \/ x0) /\ (x1 \/ y0)).
Definition term18 (x0 : Prop) := and ((~ False) \/ x0).
Definition term14 (x0 : Prop) := and ((~ True) \/ x0).
Definition term4 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (@COND Prop y0 x0 x1) = (((~ y0) \/ x0) /\ (y0 \/ x1))) True.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (@COND Prop y0 x0 x1) = (((~ y0) \/ x0) /\ (y0 \/ x1))) x2).
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((~ x1) \/ x0) /\ (x1 \/ x2).
