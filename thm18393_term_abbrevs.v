Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, ~ (x0 y0)) \/ (exists y0 : a0, exists y1 : a0, (x0 y0) /\ ((x0 y1) /\ (~ (y1 = y0)))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := ~ (@ex1 a0 x0).
