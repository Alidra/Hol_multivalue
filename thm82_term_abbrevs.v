Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : Prop) := (x0 -> False) /\ (False -> x0).
Definition term1 (x0 : Prop) := (fun y0 : Prop => y0) x0.
Definition term0 := forall y0 : Prop, y0.
Definition term3 (x0 : Prop) := (~ x0) -> x0 = False.
