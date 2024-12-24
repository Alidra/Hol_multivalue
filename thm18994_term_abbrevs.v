Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : Prop, ((exists y1 : a0, x0 y1) \/ y0) = (exists y1 : a0, (x0 y1) \/ y0).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : Prop, ((exists y2 : a0, y0 y2) \/ y1) = (exists y2 : a0, (y0 y2) \/ y1)) x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => ((exists y1 : a0, x0 y1) \/ y0) = (exists y1 : a0, (x0 y1) \/ y0)) x1.
