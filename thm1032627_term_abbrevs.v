Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : Prop) := imp (~ x0).
Definition term3 (x0 : Prop) (x1 : Prop) := (x0 -> False) -> ((~ x1) = x0) -> x1.
Definition term2 (x0 : Prop) (x1 : Prop) := ((~ x1) = x0) -> x1.
Definition term0 (x0 : Prop) := imp (x0 -> False).
Definition term4 (x0 : Prop) (x1 : Prop) := (~ x0) -> ((~ x1) = x0) -> x1.
