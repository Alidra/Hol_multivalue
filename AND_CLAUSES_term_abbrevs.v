Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : Prop) := (x0 /\ True) -> x0.
Definition term10 (x0 : Prop) := False -> x0 /\ False.
Definition term16 (x0 : Prop) := ((False /\ x0) = False) /\ (((x0 /\ False) = False) /\ ((x0 /\ x0) = x0)).
Definition term5 (x0 : Prop) := ((x0 /\ True) -> x0) /\ (x0 -> x0 /\ True).
Definition term19 := forall y0 : Prop, ((True /\ y0) = y0) /\ (((y0 /\ True) = y0) /\ (((False /\ y0) = False) /\ (((y0 /\ False) = False) /\ ((y0 /\ y0) = y0)))).
Definition term6 (x0 : Prop) := (False /\ x0) -> False.
Definition term11 (x0 : Prop) := ((x0 /\ False) -> False) /\ (False -> x0 /\ False).
Definition term14 (x0 : Prop) := ((x0 /\ x0) -> x0) /\ (x0 -> x0 /\ x0).
Definition term17 (x0 : Prop) := ((x0 /\ True) = x0) /\ (((False /\ x0) = False) /\ (((x0 /\ False) = False) /\ ((x0 /\ x0) = x0))).
Definition term0 (x0 : Prop) := (True /\ x0) -> x0.
Definition term12 (x0 : Prop) := (x0 /\ x0) -> x0.
Definition term8 (x0 : Prop) := ((False /\ x0) -> False) /\ (False -> False /\ x0).
Definition term9 (x0 : Prop) := (x0 /\ False) -> False.
Definition term1 (x0 : Prop) := x0 -> True /\ x0.
Definition term2 (x0 : Prop) := ((True /\ x0) -> x0) /\ (x0 -> True /\ x0).
Definition term13 (x0 : Prop) := x0 -> x0 /\ x0.
Definition term7 (x0 : Prop) := False -> False /\ x0.
Definition term18 (x0 : Prop) := ((True /\ x0) = x0) /\ (((x0 /\ True) = x0) /\ (((False /\ x0) = False) /\ (((x0 /\ False) = False) /\ ((x0 /\ x0) = x0)))).
Definition term15 (x0 : Prop) := ((x0 /\ False) = False) /\ ((x0 /\ x0) = x0).
Definition term4 (x0 : Prop) := x0 -> x0 /\ True.
