Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : real -> Prop) := (fun y0 : real -> Prop => (inf y0) = (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) -> real_le y2 y1)))) x0.
Definition term3 := forall y0 : real -> Prop, (inf y0) = (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) -> real_le y2 y1))).
Definition term0 := fun y0 : real -> Prop => @ε real (fun y1 : real => (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) -> real_le y2 y1)).
Definition term2 (x0 : real -> Prop) := @ε real (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y0 y1) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y1 y2) -> real_le y1 y0)).
Definition term1 (x0 : real -> Prop) := (fun y0 : real -> Prop => @ε real (fun y1 : real => (forall y2 : real, (@IN real y2 y0) -> real_le y1 y2) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y2 y3) -> real_le y2 y1))) x0.
