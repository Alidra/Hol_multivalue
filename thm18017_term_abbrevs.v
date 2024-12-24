Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (~ (@ex1 a0 x0)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (~ (@ex1 a0 (fun y0 : a0 => x0 y0))).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := ~ (@ex1 a0 (fun y0 : a0 => x0 y0)).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := @ex1 a0 (fun y0 : a0 => x0 y0).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, ~ (x0 y0)) \/ (exists y0 : a0, exists y1 : a0, (x0 y0) /\ ((x0 y1) /\ (~ (y1 = y0)))).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := ~ (@ex1 a0 x0).
