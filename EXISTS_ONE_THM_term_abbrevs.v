Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (x0 : unit -> Prop) := (fun y0 : unit => ~ (x0 y0)) tt.
Definition term16 := @eq Prop (~ False).
Definition term5 (x0 : Prop) := fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0)).
Definition term14 (x0 : Prop) := @eq Prop (False = x0).
Definition term13 (x0 : Prop) := ~ (~ x0).
Definition term28 (x0 : unit -> Prop) := @eq Prop (forall y0 : unit, (fun y1 : unit => ~ (x0 y1)) y0).
Definition term21 (x0 : unit -> Prop) := forall y0 : unit, x0 y0.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term11 (x0 : Prop) := @eq Prop (True = x0).
Definition term30 (x0 : unit -> Prop) := @eq Prop (~ (exists y0 : unit, x0 y0)).
Definition term9 (x0 : Prop) (x1 : Prop) := @eq Prop ((x0 = x1) = ((~ x0) = (~ x1))).
Definition term22 (x0 : unit -> Prop) := forall y0 : unit, (fun y1 : unit => ~ (x0 y1)) y0.
Definition term19 (x0 : unit -> Prop) := ~ (x0 tt).
Definition term24 (x0 : unit -> Prop) := fun y0 : unit => ~ (x0 y0).
Definition term6 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) x1.
Definition term18 (x0 : unit -> Prop) := ~ (exists y0 : unit, x0 y0).
Definition term10 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) False.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term15 (x0 : Prop) := @eq Prop (~ x0).
Definition term31 (x0 : unit -> Prop) := @eq Prop (~ (x0 tt)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term8 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) x1).
Definition term25 (x0 : unit -> Prop) (x1 : unit) := (fun y0 : unit => ~ (x0 y0)) x1.
Definition term12 := @eq Prop (~ True).
Definition term4 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term29 (x0 : unit -> Prop) := @eq Prop (forall y0 : unit, ~ (x0 y0)).
Definition term27 (x0 : unit -> Prop) := fun y0 : unit => (fun y1 : unit => ~ (x0 y1)) y0.
Definition term7 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) True.
Definition term3 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term26 (x0 : unit -> Prop) (x1 : unit) := ~ (x0 x1).
Definition term20 (x0 : unit -> Prop) := forall y0 : unit, ~ (x0 y0).
Definition term17 (x0 : unit -> Prop) := exists y0 : unit, x0 y0.
