Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 (@INTER a0 x0 x1)) = ((@IN a0 y0 x0) /\ (@IN a0 y0 x1))) x2.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@INTER a0 x0 y0)) = ((@IN a0 y1 x0) /\ (@IN a0 y1 y0))) x1.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@INTER a0 y0 y1)) = ((@IN a0 y2 y0) /\ (@IN a0 y2 y1))) x0.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 x0 x1)) = ((@IN a0 y0 x0) /\ (@IN a0 y0 x1)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@INTER a0 x0 y0)) = ((@IN a0 y1 x0) /\ (@IN a0 y1 y0)).
