Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (((y0 = False) -> x0 = x2) /\ ((y0 = True) -> x0 = x1)) -> x0 = (((~ y0) \/ x1) /\ (y0 \/ x2))) True.
Definition term0 (x0 : Prop) (x1 : Prop) (x2 : Prop) := fun y0 : Prop => (((y0 = False) -> x0 = x2) /\ ((y0 = True) -> x0 = x1)) -> x0 = (((~ y0) \/ x1) /\ (y0 \/ x2)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop ((((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = (((~ x2) \/ x1) /\ (x2 \/ x3))).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = (((~ x2) \/ x1) /\ (x2 \/ x3)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := @eq Prop ((fun y0 : Prop => (((y0 = False) -> x0 = x2) /\ ((y0 = True) -> x0 = x1)) -> x0 = (((~ y0) \/ x1) /\ (y0 \/ x2))) x3).
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((y0 = False) -> x0 = x2) /\ ((y0 = True) -> x0 = x1)) -> x0 = (((~ y0) \/ x1) /\ (y0 \/ x2))) x3.
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (((True = False) -> x0 = x2) /\ ((True = True) -> x0 = x1)) -> x0 = (((~ True) \/ x1) /\ (True \/ x2)).
