Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : Prop) := (fun y0 : Prop => y0) x0.
Definition term0 := forall y0 : Prop, y0.