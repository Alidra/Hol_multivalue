Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => fun y1 : a0 -> Prop => @GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (exists y4 : a0, (@IN a0 y4 y1) /\ (y3 = (y0 y4))) y3)) x0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (exists y3 : a0, (@IN a0 y3 y0) /\ (y2 = (x0 y3))) y2)) x1.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> Prop => @GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (exists y3 : a0, (@IN a0 y3 y0) /\ (y2 = (x0 y3))) y2).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := @GSPEC a1 (fun y0 : a1 => exists y1 : a1, @SETSPEC a1 y0 (exists y2 : a0, (@IN a0 y2 x0) /\ (y1 = (x1 y2))) y1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IMAGE a0 a1 x0 y0) = (@GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (exists y3 : a0, (@IN a0 y3 y0) /\ (y2 = (x0 y3))) y2))) x1.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => fun y1 : a0 -> Prop => @GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (exists y4 : a0, (@IN a0 y4 y1) /\ (y3 = (y0 y4))) y3).
Definition term10 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (@IMAGE a0 a1 y1 y0) = (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (exists y4 : a0, (@IN a0 y4 y0) /\ (y3 = (y1 y4))) y3)).
Definition term6 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (@IMAGE a0 a1 y0 y1) = (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (exists y4 : a0, (@IN a0 y4 y1) /\ (y3 = (y0 y4))) y3)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, (@IMAGE a0 a1 y0 x0) = (@GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (exists y3 : a0, (@IN a0 y3 x0) /\ (y2 = (y0 y3))) y2)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, (@IMAGE a0 a1 x0 y0) = (@GSPEC a1 (fun y1 : a1 => exists y2 : a1, @SETSPEC a1 y1 (exists y3 : a0, (@IN a0 y3 y0) /\ (y2 = (x0 y3))) y2)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@IMAGE a0 a1 y0 y1) = (@GSPEC a1 (fun y2 : a1 => exists y3 : a1, @SETSPEC a1 y2 (exists y4 : a0, (@IN a0 y4 y1) /\ (y3 = (y0 y4))) y3))) x0.
