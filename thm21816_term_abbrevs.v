Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : Prop) := ~ (~ x0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term3 := forall y0 : Prop, y0 -> (~ y0) -> False.
Definition term2 (x0 : Prop) := x0 -> (~ x0) -> False.
