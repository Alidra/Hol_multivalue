Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : unit -> Prop) := forall y0 : unit, x0 y0.
Definition term1 (x0 : unit -> Prop) := imp (x0 tt).
Definition term12 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term14 (x0 : unit -> Prop) := (x0 tt) -> x0 tt.
Definition term7 (x0 : unit -> Prop) := (x0 tt) -> forall y0 : unit, x0 tt.
Definition term5 (x0 : unit -> Prop) := forall y0 : unit, x0 tt.
Definition term16 := forall y0 : unit -> Prop, True.
Definition term0 (x0 : unit) := (fun y0 : unit => y0 = tt) x0.
Definition term13 (x0 : Prop) := forall y0 : unit, x0.
Definition term9 := fun y0 : unit -> Prop => (y0 tt) -> forall y1 : unit, y0 tt.
Definition term8 := fun y0 : unit -> Prop => (y0 tt) -> forall y1 : unit, y0 y1.
Definition term6 (x0 : unit -> Prop) := (x0 tt) -> forall y0 : unit, x0 y0.
Definition term2 (x0 : unit -> Prop) := fun y0 : unit => x0 y0.
Definition term3 (x0 : unit -> Prop) := fun y0 : unit => x0 tt.
Definition term17 (x0 : Prop) := forall y0 : unit -> Prop, x0.
Definition term11 := forall y0 : unit -> Prop, (y0 tt) -> forall y1 : unit, y0 tt.
Definition term10 := forall y0 : unit -> Prop, (y0 tt) -> forall y1 : unit, y0 y1.
Definition term15 := fun y0 : unit -> Prop => True.
