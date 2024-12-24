Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : real -> Prop) := forall y0 : real, (has_sup x0 y0) = (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) = (real_le y0 y1)).
Definition term8 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (has_sup x0 y0) = (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) = (real_le y0 y1))) x1.
Definition term7 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, (has_sup y0 y1) = (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) = (real_le y1 y2))) x0.
Definition term4 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) = (real_le x1 y0).
Definition term2 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) = (real_le y0 y1).
Definition term3 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) = (real_le y0 y1)) x1.
Definition term6 := forall y0 : real -> Prop, forall y1 : real, (has_sup y0 y1) = (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) = (real_le y1 y2)).
Definition term0 := fun y0 : real -> Prop => fun y1 : real => forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) = (real_le y1 y2).
Definition term1 (x0 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : real => forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) = (real_le y1 y2)) x0.
