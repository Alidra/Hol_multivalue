Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term2 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x0 /\ x1) -> x2) -> x0 -> x1 -> x2.
Definition term3 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 -> x1 -> x2) -> (x0 /\ x1) -> x2.
Definition term0 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (((x0 /\ x1) -> x2) -> x0 -> x1 -> x2) /\ ((x0 -> x1 -> x2) -> (x0 /\ x1) -> x2).
