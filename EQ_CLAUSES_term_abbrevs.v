Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : Prop) := x0 -> True = x0.
Definition term15 (x0 : Prop) := ((x0 = True) -> x0) /\ (x0 -> x0 = True).
Definition term16 (x0 : Prop) := (False = x0) -> x0 -> False.
Definition term21 (x0 : Prop) := (fun y0 : Prop => y0 -> False) x0.
Definition term37 := forall y0 : Prop, ((True = y0) = y0) /\ (((y0 = True) = y0) /\ (((False = y0) = (~ y0)) /\ ((y0 = False) = (~ y0)))).
Definition term25 (x0 : Prop) := ((False = x0) -> ~ x0) /\ ((~ x0) -> False = x0).
Definition term4 (x0 : Prop) := (True = x0) -> x0.
Definition term3 (x0 : Prop) := (x0 -> True) -> (True -> x0) -> x0.
Definition term18 (x0 : Prop) := (False -> x0) -> False.
Definition term31 (x0 : Prop) := (x0 -> False) /\ (False -> x0).
Definition term19 (x0 : Prop) := (x0 -> False) -> (False -> x0) -> False.
Definition term26 (x0 : Prop) := (x0 = False) -> False -> x0.
Definition term30 (x0 : Prop) := (x0 = False) -> ~ x0.
Definition term23 (x0 : Prop) := (False -> x0) /\ (x0 -> False).
Definition term27 (x0 : Prop) := (x0 = False) -> x0 -> False.
Definition term1 (x0 : Prop) := (True = x0) -> True -> x0.
Definition term22 (x0 : Prop) := @eq Prop (~ x0).
Definition term11 (x0 : Prop) := (True -> x0) -> (x0 -> True) -> x0.
Definition term13 (x0 : Prop) := (x0 -> True) /\ (True -> x0).
Definition term0 (x0 : Prop) := (True = x0) -> x0 -> True.
Definition term34 (x0 : Prop) := ((False = x0) = (~ x0)) /\ ((x0 = False) = (~ x0)).
Definition term5 (x0 : Prop) := (True -> x0) /\ (x0 -> True).
Definition term17 (x0 : Prop) := (False = x0) -> False -> x0.
Definition term35 (x0 : Prop) := ((x0 = True) = x0) /\ (((False = x0) = (~ x0)) /\ ((x0 = False) = (~ x0))).
Definition term10 (x0 : Prop) := (x0 -> True) -> x0.
Definition term8 (x0 : Prop) := (x0 = True) -> True -> x0.
Definition term12 (x0 : Prop) := (x0 = True) -> x0.
Definition term33 (x0 : Prop) := ((x0 = False) -> ~ x0) /\ ((~ x0) -> x0 = False).
Definition term14 (x0 : Prop) := x0 -> x0 = True.
Definition term7 (x0 : Prop) := ((True = x0) -> x0) /\ (x0 -> True = x0).
Definition term36 (x0 : Prop) := ((True = x0) = x0) /\ (((x0 = True) = x0) /\ (((False = x0) = (~ x0)) /\ ((x0 = False) = (~ x0)))).
Definition term20 (x0 : Prop) := (False = x0) -> ~ x0.
Definition term32 (x0 : Prop) := (~ x0) -> x0 = False.
Definition term24 (x0 : Prop) := (~ x0) -> False = x0.
Definition term28 (x0 : Prop) := (x0 -> False) -> False.
Definition term29 (x0 : Prop) := (False -> x0) -> (x0 -> False) -> False.
Definition term9 (x0 : Prop) := (x0 = True) -> x0 -> True.
Definition term2 (x0 : Prop) := (True -> x0) -> x0.
