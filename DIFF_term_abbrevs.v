Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (@IN a0 y2 y0))) y2)) x1.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@DIFF a0 x0 y0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (@IN a0 y2 y0))) y2))) x1.
Definition term0 (a0 : Type') := fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => @GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (~ (@IN a0 y3 y1))) y3).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ (@IN a0 y1 x1))) y1).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@DIFF a0 y0 y1) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (~ (@IN a0 y3 y1))) y3))) x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => @GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (@IN a0 y2 y0))) y2).
Definition term6 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@DIFF a0 y0 y1) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (~ (@IN a0 y3 y1))) y3)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@DIFF a0 x0 y0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ (@IN a0 y2 y0))) y2)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => @GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (~ (@IN a0 y3 y1))) y3)) x0.
