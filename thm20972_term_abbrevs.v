Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := or (~ True).
Definition term3 (x0 : Prop) := @eq Prop ((~ True) \/ (~ x0)).
Definition term1 (x0 : Prop) := (~ True) \/ (~ x0).
Definition term2 (x0 : Prop) := False \/ (~ x0).
Definition term4 (x0 : Prop) := @eq Prop (~ x0).
Definition term5 (x0 : Prop) := ~ (True /\ x0).
