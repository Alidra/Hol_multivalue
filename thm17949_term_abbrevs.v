Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : Prop) := forall y0 : Prop, (~ (x0 -> y0)) = (x0 /\ (~ y0)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (~ (y0 -> y1)) = (y0 /\ (~ y1))) x0.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (x0 -> y0)) = (x0 /\ (~ y0))) x1.
