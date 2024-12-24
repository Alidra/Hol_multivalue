Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0 -> Prop, (forall y1 : a0, (forall y2 : a0, (x0 y2 y1) -> y0 y2) -> y0 y1) -> forall y1 : a0, y0 y1.
