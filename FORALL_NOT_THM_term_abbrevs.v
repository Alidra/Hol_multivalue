Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, ~ (y0 y1)) = (~ (exists y1 : a0, y0 y1))) x0.
Definition term2 (a0 : Type') := fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1)).
Definition term5 (a0 : Type') := forall y0 : a0 -> Prop, (forall y1 : a0, ~ (y0 y1)) = (~ (exists y1 : a0, y0 y1)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term3 (a0 : Type') := fun y0 : a0 -> Prop => (forall y1 : a0, ~ (y0 y1)) = (~ (exists y1 : a0, y0 y1)).
Definition term4 (a0 : Type') := forall y0 : a0 -> Prop, (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1)).