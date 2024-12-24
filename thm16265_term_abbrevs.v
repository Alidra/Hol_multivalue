Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : unit -> Prop) := forall y0 : unit, x0 y0.
Definition term0 (x0 : unit -> Prop) := ((forall y0 : unit, x0 y0) -> x0 tt) /\ ((x0 tt) -> forall y0 : unit, x0 y0).
