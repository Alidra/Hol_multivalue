Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 := forall y0 : unit, True.
Definition term25 := forall y0 : unit, (one_ABS (one_REP y0)) = (one_ABS (one_REP tt)).
Definition term30 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term4 := forall y0 : unit, y0 = (one_ABS (one_REP y0)).
Definition term19 := (forall y0 : unit, (one_REP y0) = ((one_REP (one_ABS (one_REP y0))) = (one_REP y0))) -> forall y0 : unit, y0 = tt.
Definition term28 := fun y0 : unit => True.
Definition term9 (x0 : unit) := one_REP (one_ABS (one_REP x0)).
Definition term17 := imp (forall y0 : unit, one_REP y0).
Definition term12 (x0 : unit) := @eq Prop (one_REP x0).
Definition term18 := forall y0 : unit, y0 = tt.
Definition term7 := forall y0 : Prop, y0 = ((one_REP (one_ABS y0)) = y0).
Definition term15 := forall y0 : unit, one_REP y0.
Definition term0 := forall y0 : unit, (one_ABS (one_REP y0)) = y0.
Definition term26 (x0 : unit) := (fun y0 : unit => one_REP y0) x0.
Definition term1 (x0 : unit) := one_ABS (one_REP x0).
Definition term27 := @eq unit (one_ABS True).
Definition term31 (x0 : Prop) := forall y0 : unit, x0.
Definition term2 := fun y0 : unit => (one_ABS (one_REP y0)) = y0.
Definition term14 := fun y0 : unit => one_REP y0.
Definition term21 (x0 : unit) := @eq unit (one_ABS (one_REP x0)).
Definition term20 := (forall y0 : unit, one_REP y0) -> forall y0 : unit, y0 = tt.
Definition term16 := imp (forall y0 : unit, (one_REP y0) = ((one_REP (one_ABS (one_REP y0))) = (one_REP y0))).
Definition term24 := fun y0 : unit => (one_ABS (one_REP y0)) = (one_ABS (one_REP tt)).
Definition term13 := fun y0 : unit => (one_REP y0) = ((one_REP (one_ABS (one_REP y0))) = (one_REP y0)).
Definition term22 := one_ABS (one_REP tt).
Definition term3 := fun y0 : unit => y0 = (one_ABS (one_REP y0)).
Definition term6 (x0 : unit) := (fun y0 : unit => (one_ABS (one_REP y0)) = y0) x0.
Definition term10 := forall y0 : unit, (one_REP y0) = ((one_REP (one_ABS (one_REP y0))) = (one_REP y0)).
Definition term8 (x0 : unit) := (fun y0 : Prop => y0 = ((one_REP (one_ABS y0)) = y0)) (one_REP x0).
Definition term5 (x0 : unit) := (fun y0 : unit => y0 = (one_ABS (one_REP y0))) x0.
Definition term23 := fun y0 : unit => y0 = tt.
Definition term11 (x0 : unit) := @eq Prop (one_REP (one_ABS (one_REP x0))).
