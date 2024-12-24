Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := (~ True) -> True.
Definition term6 (x0 : Prop) := @eq Prop (((~ x0) -> x0) = x0).
Definition term4 (x0 : Prop) := @eq Prop ((fun y0 : Prop => ((~ y0) -> y0) = y0) x0).
Definition term5 (x0 : Prop) := (~ x0) -> x0.
Definition term0 := fun y0 : Prop => ((~ y0) -> y0) = y0.
Definition term1 (x0 : Prop) := (fun y0 : Prop => ((~ y0) -> y0) = y0) x0.
Definition term2 := (fun y0 : Prop => ((~ y0) -> y0) = y0) True.
