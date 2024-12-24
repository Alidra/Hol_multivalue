Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : Prop) := (fun y0 : Prop => ((True -> y0) = y0) /\ (((y0 -> True) = True) /\ (((False -> y0) = True) /\ (((y0 -> y0) = True) /\ ((y0 -> False) = (~ y0)))))) x0.
Definition term1 (x0 : Prop) := ((True -> x0) = x0) /\ (((x0 -> True) = True) /\ (((False -> x0) = True) /\ (((x0 -> x0) = True) /\ ((x0 -> False) = (~ x0))))).
