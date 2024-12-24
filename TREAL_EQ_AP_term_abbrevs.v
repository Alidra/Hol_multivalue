Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (y0 = y1) -> treal_eq y0 y1.
Definition term17 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (x0 = y0) -> treal_eq x0 y0.
Definition term15 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => (x0 = y0) -> treal_eq x0 y0.
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term10 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : Prop) := ((x0 = x1) -> (treal_eq x0 x1) = x2) -> ((x0 = x1) -> treal_eq x0 x1) = ((x0 = x1) -> x2).
Definition term12 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := ((x0 = x1) -> (treal_eq x0 x1) = True) -> ((x0 = x1) -> treal_eq x0 x1) = ((x0 = x1) -> True).
Definition term13 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (x0 = x1) -> treal_eq x0 x1.
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term21 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (y0 = y1) -> treal_eq y0 y1.
Definition term11 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (x0 = x1) -> (treal_eq x0 x1) = True.
Definition term7 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((x0 = x1) = x2) -> (x2 -> (treal_eq x0 x1) = y0) -> ((x0 = x1) -> treal_eq x0 x1) = (x2 -> y0)) x3.
Definition term8 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : Prop) (x3 : Prop) := ((x0 = x1) = x2) -> (x2 -> (treal_eq x0 x1) = x3) -> ((x0 = x1) -> treal_eq x0 x1) = (x2 -> x3).
Definition term0 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => treal_eq y0 y0) x0.
Definition term6 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : Prop) := forall y0 : Prop, ((x0 = x1) = x2) -> (x2 -> (treal_eq x0 x1) = y0) -> ((x0 = x1) -> treal_eq x0 x1) = (x2 -> y0).
Definition term2 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term4 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := forall y0 : Prop, forall y1 : Prop, ((x0 = x1) = y0) -> (y0 -> (treal_eq x0 x1) = y1) -> ((x0 = x1) -> treal_eq x0 x1) = (y0 -> y1).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term18 := forall y0 : prod hreal hreal, True.
Definition term9 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : Prop) := ((x0 = x1) = (x0 = x1)) -> ((x0 = x1) -> (treal_eq x0 x1) = x2) -> ((x0 = x1) -> treal_eq x0 x1) = ((x0 = x1) -> x2).
Definition term16 := fun y0 : prod hreal hreal => True.
Definition term20 (x0 : Prop) := forall y0 : prod hreal hreal, x0.
Definition term5 (x0 : prod hreal hreal) (x1 : prod hreal hreal) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((x0 = x1) = y0) -> (y0 -> (treal_eq x0 x1) = y1) -> ((x0 = x1) -> treal_eq x0 x1) = (y0 -> y1)) x2.
Definition term14 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (x0 = x1) -> True.
