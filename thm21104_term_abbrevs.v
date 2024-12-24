Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := @eq Prop (False -> ~ False).
Definition term0 := False -> ~ False.
Definition term2 (x0 : Prop) := x0 -> ~ x0.
