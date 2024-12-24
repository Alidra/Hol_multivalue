Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 = x2.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x1 -> x0) -> (x0 -> x1) -> x2.
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := ((x2 -> x3) -> x0 -> x1) /\ ((x0 -> x1) -> x2 -> x3).
Definition term1 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 -> x1.
Definition term2 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 -> x1.
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 -> x1) -> x2 -> x3.
Definition term4 (x0 : Prop) (x1 : Prop) := (x1 -> x0) -> (x0 -> x1) -> x1.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 -> x1) -> x2.
Definition term3 (x0 : Prop) (x1 : Prop) := (x0 -> x1) -> x1.
Definition term8 (x0 : Prop) (x1 : Prop) := (x1 -> x0) -> x1.
Definition term9 (x0 : Prop) (x1 : Prop) := (x0 -> x1) -> (x1 -> x0) -> x1.
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
