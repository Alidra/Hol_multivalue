Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : Prop -> Prop) := ((x0 False) /\ (x0 True)) -> forall y0 : Prop, x0 y0.
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term5 := forall y0 : Prop -> Prop, ((y0 False) /\ (y0 True)) -> forall y1 : Prop, y0 y1.
Definition term2 (x0 : Prop -> Prop) := (x0 False) /\ (x0 True).
Definition term3 (x0 : Prop -> Prop) := forall y0 : Prop, x0 y0.
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
