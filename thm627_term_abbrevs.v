Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : Prop) := ((x0 /\ x0) -> x0) /\ (x0 -> x0 /\ x0).