Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => fun y1 : a0 -> Prop => @GSPEC (prod a1 a0) (fun y2 : prod a1 a0 => exists y3 : a1, exists y4 : a0, @SETSPEC (prod a1 a0) y2 ((@IN a1 y3 y0) /\ (@IN a0 y4 y1)) (@pair a1 a0 y3 y4))) x0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@CROSS a0 a1 x0 y0) = (@GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 ((@IN a1 y2 x0) /\ (@IN a0 y3 y0)) (@pair a1 a0 y2 y3)))) x1.
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : a1 -> Prop => fun y1 : a0 -> Prop => @GSPEC (prod a1 a0) (fun y2 : prod a1 a0 => exists y3 : a1, exists y4 : a0, @SETSPEC (prod a1 a0) y2 ((@IN a1 y3 y0) /\ (@IN a0 y4 y1)) (@pair a1 a0 y3 y4)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 ((@IN a1 y2 x0) /\ (@IN a0 y3 y0)) (@pair a1 a0 y2 y3))) x1.
Definition term6 (a0 : Type') (a1 : Type') := forall y0 : a1 -> Prop, forall y1 : a0 -> Prop, (@CROSS a0 a1 y0 y1) = (@GSPEC (prod a1 a0) (fun y2 : prod a1 a0 => exists y3 : a1, exists y4 : a0, @SETSPEC (prod a1 a0) y2 ((@IN a1 y3 y0) /\ (@IN a0 y4 y1)) (@pair a1 a0 y3 y4))).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : a0 -> Prop, (@CROSS a0 a1 x0 y0) = (@GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 ((@IN a1 y2 x0) /\ (@IN a0 y3 y0)) (@pair a1 a0 y2 y3))).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := @GSPEC (prod a1 a0) (fun y0 : prod a1 a0 => exists y1 : a1, exists y2 : a0, @SETSPEC (prod a1 a0) y0 ((@IN a1 y1 x0) /\ (@IN a0 y2 x1)) (@pair a1 a0 y1 y2)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : a0 -> Prop, (@CROSS a0 a1 y0 y1) = (@GSPEC (prod a1 a0) (fun y2 : prod a1 a0 => exists y3 : a1, exists y4 : a0, @SETSPEC (prod a1 a0) y2 ((@IN a1 y3 y0) /\ (@IN a0 y4 y1)) (@pair a1 a0 y3 y4)))) x0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := fun y0 : a0 -> Prop => @GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 ((@IN a1 y2 x0) /\ (@IN a0 y3 y0)) (@pair a1 a0 y2 y3)).
