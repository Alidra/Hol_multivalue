Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
