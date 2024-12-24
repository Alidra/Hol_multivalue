Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : Prop) := False /\ (~ x0).
Definition term3 (x0 : Prop) := (~ True) /\ (~ x0).
Definition term0 (x0 : Prop) := ~ (True \/ x0).
Definition term2 := and (~ True).
Definition term1 (x0 : Prop) := @eq Prop (~ (True \/ x0)).
