Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 (x0 : Prop) := (fun y0 : Prop => y0 -> y0 \/ x0) False.
Definition term30 (x0 : Prop) (x1 : Prop) := ((~ False) \/ x1) -> x0 \/ x1.
Definition term15 (x0 : Prop) (x1 : Prop) := ((~ True) \/ x1) -> x0 \/ x1.
Definition term12 := or (~ True).
Definition term23 (x0 : Prop) (x1 : Prop) := @eq Prop (x1 -> x0 \/ x1).
Definition term4 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 \/ x0) -> ((~ y0) \/ x1) -> x0 \/ x1) True.
Definition term10 (x0 : Prop) (x1 : Prop) := (False \/ x0) -> ((~ False) \/ x1) -> x0 \/ x1.
Definition term38 (x0 : Prop) (x1 : Prop) := @eq Prop (x0 -> x0 \/ x1).
Definition term21 (x0 : Prop) := True -> x0 \/ True.
Definition term34 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => y0 -> y0 \/ x0) x1.
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (y0 \/ x0) -> ((~ y0) \/ x1) -> x0 \/ x1) x2.
Definition term9 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 \/ x0) -> ((~ y0) \/ x1) -> x0 \/ x1) False.
Definition term28 (x0 : Prop) := (~ False) \/ x0.
Definition term27 := or (~ False).
Definition term26 (x0 : Prop) := imp (False \/ x0).
Definition term11 (x0 : Prop) := imp (True \/ x0).
Definition term33 (x0 : Prop) := fun y0 : Prop => y0 -> y0 \/ x0.
Definition term13 (x0 : Prop) := (~ True) \/ x0.
Definition term2 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (y0 \/ x0) -> ((~ y0) \/ x1) -> x0 \/ x1.
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) -> ((~ x0) \/ x2) -> x1 \/ x2.
Definition term29 (x0 : Prop) := imp ((~ False) \/ x0).
Definition term14 (x0 : Prop) := imp ((~ True) \/ x0).
Definition term19 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => y0 -> x0 \/ y0) x1.
Definition term37 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => y0 -> y0 \/ x0) x1).
Definition term22 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => y0 -> x0 \/ y0) x1).
Definition term25 (x0 : Prop) := False -> x0 \/ False.
Definition term5 (x0 : Prop) (x1 : Prop) := (True \/ x0) -> ((~ True) \/ x1) -> x0 \/ x1.
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term36 (x0 : Prop) := True -> True \/ x0.
Definition term43 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, (y0 \/ y1) -> ((~ y0) \/ y2) -> y1 \/ y2.
Definition term42 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ y0) -> ((~ x0) \/ y1) -> y0 \/ y1.
Definition term31 (x0 : Prop) (x1 : Prop) := True -> x0 \/ x1.
Definition term20 (x0 : Prop) := (fun y0 : Prop => y0 -> x0 \/ y0) True.
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((x0 \/ x1) -> ((~ x0) \/ x2) -> x1 \/ x2).
Definition term32 (x0 : Prop) (x1 : Prop) := x0 -> x0 \/ x1.
Definition term41 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ x1) -> ((~ x0) \/ y0) -> x1 \/ y0.
Definition term17 (x0 : Prop) (x1 : Prop) := True -> x1 -> x0 \/ x1.
Definition term35 (x0 : Prop) := (fun y0 : Prop => y0 -> y0 \/ x0) True.
Definition term18 (x0 : Prop) := fun y0 : Prop => y0 -> x0 \/ y0.
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term40 (x0 : Prop) := False -> False \/ x0.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (y0 \/ x0) -> ((~ y0) \/ x1) -> x0 \/ x1) x2).
Definition term24 (x0 : Prop) := (fun y0 : Prop => y0 -> x0 \/ y0) False.
Definition term16 (x0 : Prop) (x1 : Prop) := x1 -> x0 \/ x1.
