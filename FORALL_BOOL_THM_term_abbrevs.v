Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : Prop -> Prop) := (x0 True) /\ (x0 False).
Definition term0 (x0 : Prop -> Prop) := forall y0 : Prop, x0 y0.