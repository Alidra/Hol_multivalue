Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 /\ (x1 /\ y0)) = ((x0 /\ x1) /\ y0).
Definition term2 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ (x1 /\ x2)) -> (x0 /\ x1) /\ x2.
Definition term0 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 /\ (x1 /\ x2).
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) /\ x2.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x0 /\ (x1 /\ x2)) -> (x0 /\ x1) /\ x2) /\ (((x0 /\ x1) /\ x2) -> x0 /\ (x1 /\ x2)).
Definition term7 := forall y0 : Prop, forall y1 : Prop, forall y2 : Prop, (y0 /\ (y1 /\ y2)) = ((y0 /\ y1) /\ y2).
Definition term6 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 /\ (y0 /\ y1)) = ((x0 /\ y0) /\ y1).
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x0 /\ x1) /\ x2) -> x0 /\ (x1 /\ x2).