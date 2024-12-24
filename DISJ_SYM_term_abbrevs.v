Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : Prop) (x1 : Prop) := ((x0 \/ x1) -> x1 \/ x0) /\ ((x1 \/ x0) -> x0 \/ x1).
Definition term3 := forall y0 : Prop, forall y1 : Prop, (y0 \/ y1) = (y1 \/ y0).
Definition term0 (x0 : Prop) (x1 : Prop) := (x1 \/ x0) -> x0 \/ x1.
Definition term2 (x0 : Prop) := forall y0 : Prop, (x0 \/ y0) = (y0 \/ x0).
