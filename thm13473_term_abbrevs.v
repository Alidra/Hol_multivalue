Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : a0) (x3 : a0) := x0 (@COND a0 x1 x2 x3).
