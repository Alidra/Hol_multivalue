Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : Prop -> Prop) := (fun y0 : Prop => x0 y0) False.
Definition term4 (x0 : Prop -> Prop) (x1 : Prop) := (fun y0 : Prop => x0 y0) x1.
Definition term6 (x0 : Prop -> Prop) := fun y0 : Prop => x0 y0.
Definition term5 (x0 : Prop -> Prop) := and (x0 True).
Definition term12 (x0 : Prop -> Prop) := (forall y0 : Prop, x0 y0) -> (x0 True) /\ (x0 False).
Definition term3 (x0 : Prop -> Prop) := (x0 True) /\ (x0 False).
Definition term13 (x0 : Prop -> Prop) := ((forall y0 : Prop, x0 y0) -> (x0 True) /\ (x0 False)) /\ (((x0 True) /\ (x0 False)) -> forall y0 : Prop, x0 y0).
Definition term1 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term8 (x0 : Prop -> Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => x0 y0) x1).
Definition term2 (x0 : Prop -> Prop) := forall y0 : Prop, x0 y0.
Definition term9 (x0 : Prop -> Prop) (x1 : Prop) := @eq Prop (x0 x1).
Definition term11 (x0 : Prop -> Prop) := ((x0 True) /\ (x0 False)) -> forall y0 : Prop, x0 y0.
Definition term0 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term7 (x0 : Prop -> Prop) := (fun y0 : Prop => x0 y0) True.
