Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 := @eq Prop (~ False).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term5 (x0 : Prop) := fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0).
Definition term16 (x0 : Prop) := @eq Prop (~ (~ x0)).
Definition term14 (x0 : Prop) := ~ (~ x0).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term22 (a0 : Type') := fun y0 : a0 -> Prop => (exists y1 : a0, ~ (y0 y1)) = (~ (forall y1 : a0, y0 y1)).
Definition term10 (x0 : Prop) := (fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0)) False.
Definition term11 (x0 : Prop) := @eq Prop (True = (~ x0)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (~ (exists y0 : a0, ~ (x0 y0))).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (~ (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0)).
Definition term44 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term40 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, x0 y0.
Definition term45 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term15 (x0 : Prop) := @eq Prop (False = (~ x0)).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term23 (a0 : Type') := fun y0 : a0 -> Prop => (~ (exists y1 : a0, ~ (y0 y1))) = (forall y1 : a0, y0 y1).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, x0 y0).
Definition term24 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0, ~ (y0 y1)) = (~ (forall y1 : a0, y0 y1)).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, (fun y1 : a0 => ~ (x0 y1)) y0).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term12 (x0 : Prop) := @eq Prop (~ x0).
Definition term6 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0)) x1.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0, x0 y0).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (fun y1 : a0 => ~ (x0 y1)) y0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term8 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0)) x1).
Definition term42 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term13 := @eq Prop (~ True).
Definition term4 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term25 (a0 : Type') := forall y0 : a0 -> Prop, (~ (exists y1 : a0, ~ (y0 y1))) = (forall y1 : a0, y0 y1).
Definition term7 (x0 : Prop) := (fun y0 : Prop => (y0 = (~ x0)) = ((~ y0) = x0)) True.
Definition term9 (x0 : Prop) (x1 : Prop) := @eq Prop ((x0 = (~ x1)) = ((~ x0) = x1)).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (~ (x0 y0)).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, ~ (x0 y0)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term3 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ ((fun y1 : a0 => ~ (x0 y1)) y0).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (~ (x0 y0)).
Definition term43 (a0 : Type') := forall y0 : a0 -> Prop, True.
