Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : Prop) := (x0 \/ False) -> x0.
Definition term6 (x0 : Prop) := (False \/ x0) -> x0.
Definition term18 (x0 : Prop) := ((True \/ x0) = True) /\ (((x0 \/ True) = True) /\ (((False \/ x0) = x0) /\ (((x0 \/ False) = x0) /\ ((x0 \/ x0) = x0)))).
Definition term4 (x0 : Prop) := True -> x0 \/ True.
Definition term17 (x0 : Prop) := ((x0 \/ True) = True) /\ (((False \/ x0) = x0) /\ (((x0 \/ False) = x0) /\ ((x0 \/ x0) = x0))).
Definition term15 (x0 : Prop) := ((x0 \/ False) = x0) /\ ((x0 \/ x0) = x0).
Definition term5 (x0 : Prop) := ((x0 \/ True) -> True) /\ (True -> x0 \/ True).
Definition term14 (x0 : Prop) := ((x0 \/ x0) -> x0) /\ (x0 -> x0 \/ x0).
Definition term0 (x0 : Prop) := (True \/ x0) -> True.
Definition term12 (x0 : Prop) := (x0 \/ x0) -> x0.
Definition term3 (x0 : Prop) := (x0 \/ True) -> True.
Definition term16 (x0 : Prop) := ((False \/ x0) = x0) /\ (((x0 \/ False) = x0) /\ ((x0 \/ x0) = x0)).
Definition term10 (x0 : Prop) := x0 -> x0 \/ False.
Definition term7 (x0 : Prop) := x0 -> False \/ x0.
Definition term2 (x0 : Prop) := ((True \/ x0) -> True) /\ (True -> True \/ x0).
Definition term1 (x0 : Prop) := True -> True \/ x0.
Definition term8 (x0 : Prop) := ((False \/ x0) -> x0) /\ (x0 -> False \/ x0).
Definition term11 (x0 : Prop) := ((x0 \/ False) -> x0) /\ (x0 -> x0 \/ False).
Definition term13 (x0 : Prop) := x0 -> x0 \/ x0.
Definition term19 := forall y0 : Prop, ((True \/ y0) = True) /\ (((y0 \/ True) = True) /\ (((False \/ y0) = y0) /\ (((y0 \/ False) = y0) /\ ((y0 \/ y0) = y0)))).