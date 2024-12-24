Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : Prop) := (x0 = False) -> ~ x0.
Definition term1 := (fun y0 : Prop => y0) False.
Definition term0 := forall y0 : Prop, y0.
