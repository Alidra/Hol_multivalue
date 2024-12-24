Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : Prop) (x1 : Prop) := (x0 \/ x1) -> x0 \/ (x0 \/ x1).
Definition term1 (x0 : Prop) (x1 : Prop) := (x0 \/ (x0 \/ x1)) -> x0 \/ x1.
Definition term0 (x0 : Prop) (x1 : Prop) := x0 \/ (x0 \/ x1).
Definition term3 (x0 : Prop) (x1 : Prop) := ((x0 \/ (x0 \/ x1)) -> x0 \/ x1) /\ ((x0 \/ x1) -> x0 \/ (x0 \/ x1)).
