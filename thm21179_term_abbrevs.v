Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (~ False) -> False.
Definition term3 (x0 : Prop) := ~ (~ x0).
Definition term4 (x0 : Prop) := (~ x0) -> x0.
Definition term2 := ~ (~ False).
Definition term1 := ~ ((~ False) -> False).
