Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : unit -> Prop) := forall y0 : unit, x0 y0.
Definition term5 (x0 : unit -> Prop) := ((forall y0 : unit, x0 y0) -> x0 tt) /\ ((x0 tt) -> forall y0 : unit, x0 y0).
Definition term4 (x0 : unit -> Prop) := (forall y0 : unit, x0 y0) -> x0 tt.
Definition term0 (x0 : unit -> Prop) := (fun y0 : unit -> Prop => (y0 tt) -> forall y1 : unit, y0 y1) x0.
Definition term1 (x0 : unit -> Prop) := (x0 tt) -> forall y0 : unit, x0 y0.
Definition term3 (x0 : unit -> Prop) (x1 : unit) := (fun y0 : unit => x0 y0) x1.
