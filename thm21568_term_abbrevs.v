Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : Prop) := x0 \/ (~ True).
Definition term0 (x0 : Prop) := imp (True = x0).
Definition term2 (x0 : Prop) := (True = x0) -> x0 \/ (~ True).
