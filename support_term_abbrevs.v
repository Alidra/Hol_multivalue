Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@support a0 a1 x0 y0 y1) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (~ ((y0 y3) = (@neutral a1 x0)))) y3))) x1.
Definition term15 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, forall y2 : type1400 a1, (@support a0 a1 y2 y1 y0) = (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (~ ((y1 y4) = (@neutral a1 y2)))) y4)).
Definition term9 (a0 : Type') (a1 : Type') := forall y0 : type1400 a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (@support a0 a1 y0 y1 y2) = (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (~ ((y1 y4) = (@neutral a1 y0)))) y4)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral a1 x2)))) y1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => fun y1 : a0 -> a1 => fun y2 : a0 -> Prop => @GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (~ ((y1 y4) = (@neutral a1 y0)))) y4)) x0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := fun y0 : a0 -> a1 => fun y1 : a0 -> Prop => @GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (~ ((y0 y3) = (@neutral a1 x0)))) y3).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => fun y1 : a0 -> Prop => @GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (~ ((y0 y3) = (@neutral a1 x0)))) y3)) x1.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@support a0 a1 x1 x0 y0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (~ ((x0 y2) = (@neutral a1 x1)))) y2))) x2.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : type1400 a1 => fun y1 : a0 -> a1 => fun y2 : a0 -> Prop => @GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (~ ((y1 y4) = (@neutral a1 y0)))) y4).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) := fun y0 : a0 -> Prop => @GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (~ ((x0 y2) = (@neutral a1 x1)))) y2).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : type1400 a1, (@support a0 a1 y1 y0 x0) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (@support a0 a1 x0 y0 y1) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (~ ((y0 y3) = (@neutral a1 x0)))) y3)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : type1400 a1, (@support a0 a1 y0 x1 x0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = (@neutral a1 y0)))) y2)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) := forall y0 : a0 -> Prop, (@support a0 a1 x1 x0 y0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (~ ((x0 y2) = (@neutral a1 x1)))) y2)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => @GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (~ ((x0 y2) = (@neutral a1 x1)))) y2)) x2.
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (@support a0 a1 y0 y1 y2) = (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (~ ((y1 y4) = (@neutral a1 y0)))) y4))) x0.
